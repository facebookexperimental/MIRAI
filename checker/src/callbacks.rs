// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
#![allow(clippy::borrowed_box)]

use crate::constant_domain::ConstantValueCache;
use crate::expected_errors;
use crate::k_limits;
use crate::smt_solver::SolverStub;
use crate::summaries;
use crate::visitors::{MirVisitor, MirVisitorCrateContext};

use log::{info, warn};
use rustc::hir::def_id::DefId;
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
        compiler.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            self.output_directory.set_file_name(".summary_store");
            self.output_directory.set_extension("sled");
            let summary_store_path = String::from(self.output_directory.to_str().unwrap());
            info!("storing summaries at {}", summary_store_path);
            let mut persistent_summary_cache =
                summaries::PersistentSummaryCache::new(&tcx, summary_store_path);
            let mut constant_value_cache = ConstantValueCache::default();
            let mut defs_to_analyze: HashSet<DefId> = HashSet::from_iter(tcx.body_owners());
            let mut defs_to_reanalyze: HashSet<DefId> = HashSet::new();
            let mut defs_to_check: HashSet<DefId> = HashSet::new();
            let mut defs_to_not_reanalyze: HashSet<DefId> = HashSet::new();
            let mut diagnostics_for: HashMap<DefId, Vec<DiagnosticBuilder<'_>>> = HashMap::new();
            let mut not_done = true;
            let mut iteration_count = 0;
            while not_done && iteration_count < k_limits::MAX_OUTER_FIXPOINT_ITERATIONS {
                for def_id in tcx.body_owners() {
                    if defs_to_not_reanalyze.contains(&def_id) {
                        continue;
                    }
                    let analyze_it = defs_to_analyze.contains(&def_id);
                    let check_it = !analyze_it && defs_to_check.contains(&def_id);
                    if !analyze_it && !check_it {
                        continue;
                    }
                    not_done = true;
                    let name: String;
                    {
                        name = persistent_summary_cache.get_summary_key_for(def_id).clone();
                        if check_it {
                            info!("checking({:?})", name)
                        } else if iteration_count == 0 {
                            info!("analyzing({:?})", name);
                        } else {
                            info!("reanalyzing({:?})", name);
                        }
                    }
                    // By this time all analyses have been carried out, so it should be safe to borrow this now.
                    let old_summary_if_changed = {
                        let mir = tcx.optimized_mir(def_id);
                        // todo: #3 provide a helper that returns the solver as specified by a compiler switch.
                        let mut smt_solver = SolverStub::default();
                        let mut mir_visitor = MirVisitor::new(MirVisitorCrateContext {
                            session: compiler.session(),
                            tcx,
                            def_id,
                            mir,
                            summary_cache: &mut persistent_summary_cache,
                            constant_value_cache: &mut constant_value_cache,
                            smt_solver: &mut smt_solver,
                        });
                        let (r, analysis_time_in_seconds) = mir_visitor.visit_body(&name);
                        if analysis_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
                            // This body is beyond MIRAI for now
                            warn!(
                                "analysis of {} timed out after {} seconds",
                                name, analysis_time_in_seconds,
                            );
                            defs_to_not_reanalyze.insert(def_id);
                        }
                        fn cancel(mut db: DiagnosticBuilder<'_>) {
                            db.cancel();
                        }
                        if let Some(old_diags) =
                            diagnostics_for.insert(def_id, mir_visitor.buffered_diagnostics)
                        {
                            old_diags.into_iter().for_each(cancel)
                        }
                        r
                    };
                    if let Some(old_summary) = old_summary_if_changed {
                        // Bodies should not get checked before their summaries have reached a fixed point.
                        if check_it {
                            info!("body summary changed after it supposedly reached a fixed point");
                            info!("*********** old summary: {:?}", old_summary);
                            info!(
                                "*********** new summary: {:?}",
                                persistent_summary_cache.get_summary_for(def_id, None)
                            );
                        }
                        for dep_id in persistent_summary_cache.get_dependents(&def_id).iter() {
                            defs_to_reanalyze.insert(dep_id.clone());
                        }
                    } else {
                        // Provided that no other body that def_id depends on has changed in this round,
                        // the summary for def_id should now be at a fixed point.
                        defs_to_check.insert(def_id);
                    }
                }
                defs_to_analyze = defs_to_reanalyze;
                defs_to_reanalyze = HashSet::new();
                iteration_count += 1;
                info!("outer fixed point iteration {}", iteration_count);
            }
            if self.test_run {
                let mut expected_errors =
                    expected_errors::ExpectedErrors::new(self.file_name.as_str());
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
            info!("done with analysis");
        });
        !self.test_run // Although MIRAI is only a checker we still need code generation for build scripts.
                       // We avoid code gen for test cases because LLVM is not used in a thread safe manner.
    }
}
