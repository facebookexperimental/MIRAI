// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
#![allow(clippy::borrowed_box)]

use crate::constant_domain::ConstantValueCache;
use crate::expected_errors;
use crate::k_limits;
use crate::summaries::{PersistentSummaryCache, Summary};
use crate::visitors::{MirVisitor, MirVisitorCrateContext};
use crate::z3_solver::Z3Solver;

use log::{info, warn};
use rustc::hir::def_id::DefId;
use rustc::ty::TyCtxt;
use rustc_interface::interface;
use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;
use std::path::PathBuf;
use syntax::errors::DiagnosticBuilder;

/// Private state used to implement the callbacks.
pub struct MiraiCallbacks {
    /// The relative path of the file being compiled.
    file_name: String,
    /// A path to the directory where analysis output, such as the summary cache, should be stored.
    output_directory: PathBuf,
    /// True if this run is done via cargo test
    test_run: bool,
}

/// Constructors
impl MiraiCallbacks {
    pub fn new() -> MiraiCallbacks {
        MiraiCallbacks {
            file_name: String::new(),
            output_directory: PathBuf::default(),
            test_run: false,
        }
    }

    pub fn test_runner() -> MiraiCallbacks {
        MiraiCallbacks {
            file_name: String::new(),
            output_directory: PathBuf::default(),
            test_run: true,
        }
    }
}
impl Default for MiraiCallbacks {
    fn default() -> Self {
        Self::new()
    }
}

impl rustc_driver::Callbacks for MiraiCallbacks {
    /// Called before creating the compiler instance
    fn config(&mut self, config: &mut interface::Config) {
        config.crate_cfg.insert(("mirai".to_string(), None));
        self.file_name = config.input.source_name().to_string();
        info!("Processing input file: {}", self.file_name);
        match &config.output_dir {
            None => self
                .output_directory
                .push(std::env::temp_dir().to_str().unwrap()),
            Some(path_buf) => self.output_directory.push(path_buf.as_path()),
        };
    }

    /// Called after the compiler has completed all analysis passes and before it lowers MIR to LLVM IR.
    /// At this point the compiler is ready to tell us all it knows and we can proceed to do abstract
    /// interpretation of all of the functions that will end up in the compiler output.
    /// If this method returns false, the compilation will stop.
    fn after_analysis(&mut self, compiler: &interface::Compiler) -> bool {
        compiler.session().abort_if_errors();
        if self.output_directory.to_str().unwrap().contains("/build/") {
            // No need to analyze a build script, but do generate code.
            return true;
        }
        compiler
            .global_ctxt()
            .unwrap()
            .peek_mut()
            .enter(|tcx| self.analyze_with_mirai(compiler, &tcx));
        !self.test_run // Although MIRAI is only a checker, cargo still needs code generation to work.
                       // We avoid code gen for test cases because LLVM is not used in a thread safe manner.
    }
}

struct DefSets {
    defs_to_analyze: HashSet<DefId>,
    defs_to_reanalyze: HashSet<DefId>,
    defs_to_not_reanalyze: HashSet<DefId>,
}

impl MiraiCallbacks {
    /// Analyze the crate currently being compiled, using the information given in compiler and tcx.
    fn analyze_with_mirai<'a, 'tcx: 'a>(
        &mut self,
        compiler: &interface::Compiler,
        tcx: &'a TyCtxt<'a, 'tcx, 'tcx>,
    ) {
        self.output_directory.set_file_name(".summary_store");
        self.output_directory.set_extension("sled");
        let summary_store_path = String::from(self.output_directory.to_str().unwrap());
        info!(
            "storing summaries for {} at {}",
            self.file_name, summary_store_path
        );
        let mut persistent_summary_cache = PersistentSummaryCache::new(tcx, summary_store_path);
        let mut constant_value_cache = ConstantValueCache::default();
        let mut def_sets = DefSets {
            defs_to_analyze: HashSet::from_iter(tcx.body_owners()),
            defs_to_reanalyze: HashSet::new(),
            defs_to_not_reanalyze: HashSet::new(),
        };
        let mut diagnostics_for: HashMap<DefId, Vec<DiagnosticBuilder<'_>>> = HashMap::new();
        for iteration_count in 1..=k_limits::MAX_OUTER_FIXPOINT_ITERATIONS {
            info!("outer fixed point iteration {}", iteration_count);
            Self::analyze_bodies(
                compiler,
                tcx,
                &mut persistent_summary_cache,
                &mut constant_value_cache,
                &mut def_sets,
                &mut diagnostics_for,
                iteration_count,
            );
            if def_sets.defs_to_reanalyze.is_empty() {
                info!("done with analysis");
                break;
            }
            let defs_to_reanalyze = def_sets.defs_to_reanalyze;
            def_sets.defs_to_reanalyze = HashSet::new();
            def_sets.defs_to_analyze = defs_to_reanalyze;
            info!(" ");
        }
        self.emit_or_check_diagnostics(&mut diagnostics_for);
    }

    /// Analyze each function body in the crate that does not yet have a summary that has reached
    /// a fixed point and add them to. The set of such functions are provided by def_sets.defs_to_analyze.
    /// Also analyze function bodies in the def_sets.defs_to_check set, which are those bodies
    /// whose summaries reached a fixed point during the previous call to this function.
    /// Returns true if all summaries have reached a fixed point after this call.
    /// If a summary has changed from the previous iteration (i.e. not reached a fixed point), add
    /// the def_id of the function, as well as the def_id of any function that calls the function,
    /// to def_sets.defs_to_reanalyze.
    fn analyze_bodies<'a, 'tcx: 'a>(
        compiler: &'a interface::Compiler,
        tcx: &'a TyCtxt<'a, 'tcx, 'tcx>,
        mut persistent_summary_cache: &mut PersistentSummaryCache<'a, 'tcx>,
        mut constant_value_cache: &mut ConstantValueCache,
        def_sets: &mut DefSets,
        diagnostics_for: &mut HashMap<DefId, Vec<DiagnosticBuilder<'a>>>,
        iteration_count: usize,
    ) {
        for def_id in tcx.body_owners() {
            if def_sets.defs_to_not_reanalyze.contains(&def_id) {
                // Analysis of this body time-out previously, so there is no previous summary
                // and no expectation that this time it won't time out again. Just ignore it for
                // now.
                continue;
            }
            if !def_sets.defs_to_analyze.contains(&def_id) {
                // The function summary reached a fixed point in the previous iteration
                // as have all of the function summaries that this function depends on.
                continue;
            }
            let name = MiraiCallbacks::get_and_log_name(
                &mut persistent_summary_cache,
                iteration_count,
                def_id,
            );
            let old_summary_if_changed = {
                let mut buffered_diagnostics: Vec<DiagnosticBuilder<'_>> = vec![];
                let (r, analysis_time_in_seconds) = Self::visit_body(
                    def_id,
                    &name,
                    compiler,
                    tcx,
                    &mut constant_value_cache,
                    &mut persistent_summary_cache,
                    &mut buffered_diagnostics,
                );
                if analysis_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
                    // This body is beyond MIRAI for now
                    warn!(
                        "analysis of {} timed out after {} seconds",
                        name, analysis_time_in_seconds,
                    );
                    // Prevent the function from being analyzed again.
                    def_sets.defs_to_not_reanalyze.insert(def_id);
                }
                // We want diagnostics even for function that are not yet a fixed point, since
                // the outer fixed point loop currently diverges in many cases.
                fn cancel(mut db: DiagnosticBuilder<'_>) {
                    db.cancel();
                }
                if let Some(old_diags) = diagnostics_for.insert(def_id, buffered_diagnostics) {
                    old_diags.into_iter().for_each(cancel)
                }
                r
            };
            MiraiCallbacks::select_defs_to_reanalyze(
                &mut persistent_summary_cache,
                &mut def_sets.defs_to_reanalyze,
                def_id,
                old_summary_if_changed,
            )
        }
    }

    /// Add def_id (and its dependents) to defs_to_reanalyze if the old summary differs from the
    /// newly produced summary.
    fn select_defs_to_reanalyze<'a, 'tcx: 'a>(
        persistent_summary_cache: &mut PersistentSummaryCache<'a, 'tcx>,
        defs_to_reanalyze: &mut HashSet<DefId>,
        def_id: DefId,
        old_summary_if_changed: Option<Summary>,
    ) {
        if let Some(_old_summary) = old_summary_if_changed {
            // the old summary is only used during debugging.
            for dep_id in persistent_summary_cache.get_dependents(&def_id).iter() {
                defs_to_reanalyze.insert(*dep_id);
            }
            defs_to_reanalyze.insert(def_id);
        }
    }

    /// Logs the summary key of the function that is about to be analyzed.
    fn get_and_log_name<'a, 'tcx: 'a>(
        persistent_summary_cache: &mut PersistentSummaryCache<'a, 'tcx>,
        iteration_count: usize,
        def_id: DefId,
    ) -> String {
        let name: String;
        {
            name = persistent_summary_cache.get_summary_key_for(def_id).clone();
            if iteration_count == 1 {
                info!("analyzing({:?})", name);
            } else {
                info!("reanalyzing({:?})", name);
            }
        }
        name
    }

    /// The outer fixed point loop has been terminated, so emit any diagnostics or, if testing,
    /// check that they are as expected.
    fn emit_or_check_diagnostics(
        &mut self,
        diagnostics_for: &mut HashMap<DefId, Vec<DiagnosticBuilder<'_>>>,
    ) {
        if self.test_run {
            let mut expected_errors = expected_errors::ExpectedErrors::new(self.file_name.as_str());
            let mut diags = vec![];
            diagnostics_for.values_mut().flatten().for_each(|db| {
                db.cancel();
                db.clone().buffer(&mut diags)
            });
            expected_errors.check_messages(diags);
        } else {
            fn emit(db: &mut DiagnosticBuilder<'_>) {
                db.emit();
            }
            diagnostics_for.values_mut().flatten().for_each(emit);
        }
    }

    /// Run the abstract interpreter over the function body and produce a summary of its effects
    /// and collect any diagnostics into the buffer.
    fn visit_body<'a, 'b, 'tcx: 'b>(
        def_id: DefId,
        name: &str,
        compiler: &'b interface::Compiler,
        tcx: &'b TyCtxt<'b, 'tcx, 'tcx>,
        mut constant_value_cache: &'a mut ConstantValueCache,
        mut persistent_summary_cache: &'a mut PersistentSummaryCache<'b, 'tcx>,
        mut buffered_diagnostics: &'a mut Vec<DiagnosticBuilder<'b>>,
    ) -> (Option<Summary>, u64) {
        let mir = tcx.optimized_mir(def_id);
        // todo: #3 provide a helper that returns the solver as specified by a compiler switch.
        let mut smt_solver = Z3Solver::default();
        let mut mir_visitor = MirVisitor::new(MirVisitorCrateContext {
            session: compiler.session(),
            tcx,
            def_id,
            mir,
            summary_cache: &mut persistent_summary_cache,
            constant_value_cache: &mut constant_value_cache,
            smt_solver: &mut smt_solver,
            buffered_diagnostics: &mut buffered_diagnostics,
        });
        mir_visitor.visit_body(&name)
    }
}
