// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
#![allow(clippy::borrowed_box)]

use crate::constant_domain::ConstantValueCache;
use crate::expected_errors;
use crate::summaries::PersistentSummaryCache;
use crate::utils;
use crate::visitors::{MirVisitor, MirVisitorCrateContext};
use crate::z3_solver::Z3Solver;

use log::info;
use log_derive::{logfn, logfn_inputs};
use rustc::hir::def_id::DefId;
use rustc::ty::TyCtxt;
use rustc_driver::Compilation;
use rustc_interface::interface;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter, Result};
use std::iter::FromIterator;
use std::ops::Deref;
use std::path::PathBuf;
use std::rc::Rc;
use syntax::errors::{Diagnostic, DiagnosticBuilder};
use tempdir::TempDir;

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

impl Debug for MiraiCallbacks {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "MiraiCallbacks".fmt(f)
    }
}

impl Default for MiraiCallbacks {
    fn default() -> Self {
        Self::new()
    }
}

impl rustc_driver::Callbacks for MiraiCallbacks {
    /// Called before creating the compiler instance
    #[logfn(TRACE)]
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
    #[logfn(TRACE)]
    fn after_analysis(&mut self, compiler: &interface::Compiler) -> Compilation {
        compiler.session().abort_if_errors();
        if self
            .output_directory
            .to_str()
            .expect("valid string")
            .contains("/build/")
        {
            // No need to analyze a build script, but do generate code.
            return Compilation::Continue;
        }
        compiler
            .global_ctxt()
            .unwrap()
            .peek_mut()
            .enter(|tcx| self.analyze_with_mirai(compiler, tcx));
        if self.test_run {
            // We avoid code gen for test cases because LLVM is not used in a thread safe manner.
            Compilation::Stop
        } else {
            // Although MIRAI is only a checker, cargo still needs code generation to work.
            Compilation::Continue
        }
    }
}

struct AnalysisInfo<'compilation, 'tcx> {
    persistent_summary_cache: PersistentSummaryCache<'tcx>,
    constant_value_cache: ConstantValueCache<'tcx>,
    diagnostics_for: HashMap<DefId, Vec<DiagnosticBuilder<'compilation>>>,
    analyze_single_func: Option<String>,
}

impl MiraiCallbacks {
    /// Analyze the crate currently being compiled, using the information given in compiler and tcx.
    #[logfn(TRACE)]
    fn analyze_with_mirai(&mut self, compiler: &interface::Compiler, tcx: TyCtxt<'_>) {
        let output_dir = String::from(self.output_directory.to_str().expect("valid string"));
        let summary_store_path = if std::env::var("MIRAI_SHARE_PERSISTENT_STORE").is_ok() {
            output_dir
        } else {
            let temp_dir = TempDir::new("mirai_temp_dir").expect("failed to create a temp dir");
            String::from(temp_dir.into_path().to_str().expect("valid string"))
        };
        info!(
            "storing summaries for {} at {}/.summary_store.sled",
            self.file_name, summary_store_path
        );
        let persistent_summary_cache = PersistentSummaryCache::new(tcx, summary_store_path);
        let defs = Vec::from_iter(tcx.body_owners());
        let constant_value_cache = ConstantValueCache::default();
        let diagnostics_for: HashMap<DefId, Vec<DiagnosticBuilder<'_>>> = HashMap::new();
        let mut analysis_info = AnalysisInfo {
            persistent_summary_cache,
            constant_value_cache,
            diagnostics_for,
            analyze_single_func: self.analyze_single_func.to_owned(),
        };
        Self::analyze_bodies(compiler, tcx, &defs, &mut analysis_info);
        if !self.emit_or_check_diagnostics(&mut analysis_info.diagnostics_for) {
            compiler.session().fatal("test failed");
        }
    }

    /// Emit any diagnostics or, if testing, check that they are as expected.
    #[logfn_inputs(TRACE)]
    fn emit_or_check_diagnostics<'compilation>(
        &mut self,
        diagnostics_for: &mut HashMap<DefId, Vec<DiagnosticBuilder<'compilation>>>,
    ) -> bool {
        if self.test_run {
            let mut expected_errors = expected_errors::ExpectedErrors::new(self.file_name.as_str());
            let mut diags = vec![];
            diagnostics_for.values_mut().flatten().for_each(|db| {
                db.cancel();
                db.clone().buffer(&mut diags)
            });
            expected_errors.check_messages(diags)
        } else {
            let mut diagnostics: Vec<&mut DiagnosticBuilder<'compilation>> =
                diagnostics_for.values_mut().flatten().collect();
            fn compare_diagnostics<'compilation>(
                x: &&mut DiagnosticBuilder<'compilation>,
                y: &&mut DiagnosticBuilder<'compilation>,
            ) -> Ordering {
                let xd: &Diagnostic = x.deref();
                let yd: &Diagnostic = y.deref();
                if xd.span.primary_spans().lt(&yd.span.primary_spans()) {
                    Ordering::Less
                } else if xd.span.primary_spans().gt(&yd.span.primary_spans()) {
                    Ordering::Greater
                } else {
                    Ordering::Equal
                }
            }
            diagnostics.sort_by(compare_diagnostics);
            fn emit(db: &mut DiagnosticBuilder<'_>) {
                db.emit();
            }
            diagnostics.into_iter().for_each(emit);
            true
        }
    }

    /// Analyze all of the bodies in the crate that is being compiled.
    #[logfn(TRACE)]
    fn analyze_bodies<'analysis, 'tcx>(
        compiler: &'analysis interface::Compiler,
        tcx: TyCtxt<'tcx>,
        defs: &[DefId],
        analysis_info: &mut AnalysisInfo<'analysis, 'tcx>,
    ) {
        // Analyze all public methods
        for def_id in defs.iter() {
            if !utils::is_public(*def_id, tcx) {
                continue;
            }
            MiraiCallbacks::analyze_body(compiler, tcx, analysis_info, *def_id);
        }
        // Analyze non public methods that have not been called in this crate.
        for def_id in defs.iter() {
            if !utils::is_public(*def_id, tcx)
                && analysis_info
                    .persistent_summary_cache
                    .get_dependents(def_id)
                    .is_empty()
            {
                MiraiCallbacks::analyze_body(compiler, tcx, analysis_info, *def_id);
            }
        }
    }

    /// Analyze the given function body.
    #[logfn(TRACE)]
    fn analyze_body<'analysis, 'tcx>(
        compiler: &'analysis interface::Compiler,
        tcx: TyCtxt<'tcx>,
        analysis_info: &mut AnalysisInfo<'analysis, 'tcx>,
        def_id: DefId,
    ) {
        let name = MiraiCallbacks::get_and_log_name(
            &mut analysis_info.persistent_summary_cache,
            analysis_info.analyze_single_func.is_none(),
            1,
            def_id,
        );
        if let Some(fname) = &analysis_info.analyze_single_func {
            // If the SINGLE_FUNC=fname option was provided, skip the analysis of all
            // functions whose names don't match fname.
            if *fname != name.to_string() {
                return;
            }
        } else {
            // No need to analyze a body for which we already have a non default summary.
            // We do, however, have to allow local foreign contract functions to override
            // the standard summaries that are already in the cache.
            if !utils::is_foreign_contract(tcx, def_id) {
                let summary = analysis_info
                    .persistent_summary_cache
                    .get_summary_for(def_id, None);
                if summary.is_not_default {
                    return;
                }
            }
        }
        let mut buffered_diagnostics: Vec<DiagnosticBuilder<'_>> = vec![];
        Self::visit_body(
            def_id,
            &name,
            compiler,
            tcx,
            analysis_info,
            &mut buffered_diagnostics,
        );
        fn cancel(mut db: DiagnosticBuilder<'_>) {
            db.cancel();
        }
        if let Some(old_diags) = analysis_info
            .diagnostics_for
            .insert(def_id, buffered_diagnostics)
        {
            old_diags.into_iter().for_each(cancel)
        }
    }

    /// Logs the summary key of the function that is about to be analyzed.
    #[logfn_inputs(TRACE)]
    fn get_and_log_name(
        persistent_summary_cache: &mut PersistentSummaryCache<'_>,
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

    /// Run the abstract interpreter over the function body and produce a summary of its effects
    /// and collect any diagnostics into the buffer.
    #[logfn(TRACE)]
    fn visit_body<'analysis, 'compilation, 'tcx>(
        def_id: DefId,
        name: &str,
        compiler: &'compilation interface::Compiler,
        tcx: TyCtxt<'tcx>,
        analysis_info: &'analysis mut AnalysisInfo<'compilation, 'tcx>,
        mut buffered_diagnostics: &'analysis mut Vec<DiagnosticBuilder<'compilation>>,
    ) {
        let mir = tcx.optimized_mir(def_id);
        let mut smt_solver = Z3Solver::default();
        analysis_info.constant_value_cache.reset_heap_counter();
        let mut mir_visitor = MirVisitor::new(MirVisitorCrateContext {
            session: compiler.session(),
            tcx,
            def_id,
            mir,
            summary_cache: &mut analysis_info.persistent_summary_cache,
            constant_value_cache: &mut analysis_info.constant_value_cache,
            smt_solver: &mut smt_solver,
            buffered_diagnostics: &mut buffered_diagnostics,
        });
        mir_visitor.visit_body(&name, &[]);
    }
}
