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
use std::rc::Rc;
use syntax::errors::DiagnosticBuilder;

/// Private state used to implement the callbacks.
pub struct MiraiCallbacks {
    /// The relative path of the file being compiled.
    file_name: String,
    /// A path to the directory where analysis output, such as the summary cache, should be stored.
    output_directory: PathBuf,
    /// True if this run is done via cargo test
    test_run: bool,
    /// If a function name is given, only analyze that function
    pub analyze_single_func: Option<String>,
}

/// Constructors
impl MiraiCallbacks {
    pub fn new() -> MiraiCallbacks {
        MiraiCallbacks {
            file_name: String::new(),
            output_directory: PathBuf::default(),
            test_run: false,
            analyze_single_func: None,
        }
    }

    pub fn test_runner() -> MiraiCallbacks {
        MiraiCallbacks {
            file_name: String::new(),
            output_directory: PathBuf::default(),
            test_run: true,
            analyze_single_func: None,
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
            None => {
                self.output_directory = std::env::temp_dir();
                self.output_directory.pop();
            }
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

struct AnalysisInfo<'a, 'tcx> {
    persistent_summary_cache: PersistentSummaryCache<'a, 'tcx>,
    constant_value_cache: ConstantValueCache<'tcx>,
    def_sets: DefSets,
    diagnostics_for: HashMap<DefId, Vec<DiagnosticBuilder<'a>>>,
    analyze_single_func: Option<String>,
}

impl MiraiCallbacks {
    /// Analyze the crate currently being compiled, using the information given in compiler and tcx.
    fn analyze_with_mirai(&mut self, compiler: &interface::Compiler, tcx: &TyCtxt<'_>) {
        let summary_store_path = String::from(self.output_directory.to_str().unwrap());
        info!(
            "storing summaries for {} at {}/.summary_store.sled",
            self.file_name, summary_store_path
        );
        let persistent_summary_cache = PersistentSummaryCache::new(tcx, summary_store_path);
        let constant_value_cache = ConstantValueCache::default();
        let def_sets = DefSets {
            defs_to_analyze: HashSet::from_iter(tcx.body_owners()),
            defs_to_reanalyze: HashSet::new(),
            defs_to_not_reanalyze: HashSet::new(),
        };
        let diagnostics_for: HashMap<DefId, Vec<DiagnosticBuilder<'_>>> = HashMap::new();
        let mut analysis_info = AnalysisInfo {
            persistent_summary_cache,
            constant_value_cache,
            def_sets,
            diagnostics_for,
            analyze_single_func: self.analyze_single_func.to_owned(),
        };
        if self.analyze_single_func.is_some() {
            Self::analyze_bodies(compiler, tcx, &mut analysis_info, 1);
        } else {
            for iteration_count in 1..=k_limits::MAX_OUTER_FIXPOINT_ITERATIONS {
                info!("outer fixed point iteration {}", iteration_count);
                Self::analyze_bodies(compiler, tcx, &mut analysis_info, iteration_count);
                if analysis_info.def_sets.defs_to_reanalyze.is_empty() {
                    info!("done with analysis");
                    break;
                }
                let defs_to_reanalyze = analysis_info.def_sets.defs_to_reanalyze;
                analysis_info.def_sets.defs_to_reanalyze = HashSet::new();
                analysis_info.def_sets.defs_to_analyze = defs_to_reanalyze;
                analysis_info
                    .persistent_summary_cache
                    .invalidate_default_summaries();
                info!(" ");
            }
        }
        self.emit_or_check_diagnostics(&mut analysis_info.diagnostics_for);
    }

    /// Analyze each function body in the crate that does not yet have a summary that has reached
    /// a fixed point and add them to. The set of such functions are provided by def_sets.defs_to_analyze.
    /// Also analyze function bodies in the def_sets.defs_to_check set, which are those bodies
    /// whose summaries reached a fixed point during the previous call to this function.
    /// Returns true if all summaries have reached a fixed point after this call.
    /// If a summary has changed from the previous iteration (i.e. not reached a fixed point), add
    /// the def_id of the function, as well as the def_id of any function that calls the function,
    /// to def_sets.defs_to_reanalyze.
    fn analyze_bodies<'a, 'tcx>(
        compiler: &'a interface::Compiler,
        tcx: &'a TyCtxt<'tcx>,
        analysis_info: &mut AnalysisInfo<'a, 'tcx>,
        iteration_count: usize,
    ) {
        for def_id in tcx.body_owners() {
            if analysis_info
                .def_sets
                .defs_to_not_reanalyze
                .contains(&def_id)
            {
                // Analysis of this body time-out previously, so there is no previous summary
                // and no expectation that this time it won't time out again. Just ignore it for
                // now.
                continue;
            }
            if !analysis_info.def_sets.defs_to_analyze.contains(&def_id) {
                // The function summary reached a fixed point in the previous iteration
                // as have all of the function summaries that this function depends on.
                continue;
            }
            let name = MiraiCallbacks::get_and_log_name(
                &mut analysis_info.persistent_summary_cache,
                analysis_info.analyze_single_func.is_none(),
                iteration_count,
                def_id,
            );
            if let Some(fname) = &analysis_info.analyze_single_func {
                // If the SINGLE_FUNC=fname option was provided, skip the analysis of all
                // functions whose names don't match fname.
                if *fname != name.to_string() {
                    continue;
                }
            };
            let old_summary_if_changed = {
                let mut buffered_diagnostics: Vec<DiagnosticBuilder<'_>> = vec![];
                let (r, analysis_time_in_seconds) = Self::visit_body(
                    def_id,
                    &name,
                    compiler,
                    tcx,
                    &mut analysis_info.constant_value_cache,
                    &mut analysis_info.persistent_summary_cache,
                    &mut buffered_diagnostics,
                );
                if analysis_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
                    // This body is beyond MIRAI for now
                    warn!(
                        "analysis of {} timed out after {} seconds",
                        name, analysis_time_in_seconds,
                    );
                    // Prevent the function from being analyzed again.
                    analysis_info.def_sets.defs_to_not_reanalyze.insert(def_id);
                }
                // We want diagnostics even for function that are not yet a fixed point, since
                // the outer fixed point loop currently diverges in many cases.
                fn cancel(mut db: DiagnosticBuilder<'_>) {
                    db.cancel();
                }
                if let Some(old_diags) = analysis_info
                    .diagnostics_for
                    .insert(def_id, buffered_diagnostics)
                {
                    old_diags.into_iter().for_each(cancel)
                }
                r
            };
            MiraiCallbacks::select_defs_to_reanalyze(
                &mut analysis_info.persistent_summary_cache,
                &mut analysis_info.def_sets.defs_to_reanalyze,
                def_id,
                old_summary_if_changed,
            )
        }
    }

    /// Add def_id (and its dependents) to defs_to_reanalyze if the old summary differs from the
    /// newly produced summary.
    fn select_defs_to_reanalyze(
        persistent_summary_cache: &mut PersistentSummaryCache<'_, '_>,
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
    fn get_and_log_name(
        persistent_summary_cache: &mut PersistentSummaryCache<'_, '_>,
        log_it: bool,
        iteration_count: usize,
        def_id: DefId,
    ) -> Rc<String> {
        let name: Rc<String>;
        {
            name = persistent_summary_cache.get_summary_key_for(def_id).clone();
            if log_it {
                if iteration_count == 1 {
                    info!("analyzing({:?})", name);
                } else {
                    info!("reanalyzing({:?})", name);
                }
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
    fn visit_body<'a, 'b, 'tcx>(
        def_id: DefId,
        name: &str,
        compiler: &'b interface::Compiler,
        tcx: &'b TyCtxt<'tcx>,
        mut constant_value_cache: &'a mut ConstantValueCache<'tcx>,
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
