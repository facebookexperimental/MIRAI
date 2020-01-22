// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
#![allow(clippy::borrowed_box)]

use crate::constant_domain::ConstantValueCache;
use crate::expected_errors;
use crate::known_names::KnownNamesCache;
use crate::options::Options;
use crate::summaries::PersistentSummaryCache;
use crate::utils;
use crate::visitors::{MirVisitor, MirVisitorCrateContext};
use crate::z3_solver::Z3Solver;

use log::info;
use log_derive::{logfn, logfn_inputs};
use rustc::mir;
use rustc::session::config::ErrorOutputType;
use rustc::session::early_error;
use rustc::ty::subst::SubstsRef;
use rustc::ty::TyCtxt;
use rustc_driver::Compilation;
use rustc_errors::{Diagnostic, DiagnosticBuilder};
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_interface::{interface, Queries};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter, Result};
use std::iter::FromIterator;
use std::ops::Deref;
use std::path::PathBuf;
use std::rc::Rc;
use tempdir::TempDir;

/// Private state used to implement the callbacks.
pub struct MiraiCallbacks {
    /// Options provided to the analysis.
    options: Options,
    /// The relative path of the file being compiled.
    file_name: String,
    /// A path to the directory where analysis output, such as the summary cache, should be stored.
    output_directory: PathBuf,
    /// True if this run is done via cargo test
    test_run: bool,
}

/// Constructors
impl MiraiCallbacks {
    pub fn new(options: Options) -> MiraiCallbacks {
        MiraiCallbacks {
            options,
            file_name: String::new(),
            output_directory: PathBuf::default(),
            test_run: false,
        }
    }

    pub fn test_runner(options: Options) -> MiraiCallbacks {
        MiraiCallbacks {
            options,
            file_name: String::new(),
            output_directory: PathBuf::default(),
            test_run: true,
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
        Self::new(Options::default())
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
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
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
        queries
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
    options: &'compilation Options,
    persistent_summary_cache: PersistentSummaryCache<'tcx>,
    constant_value_cache: ConstantValueCache<'tcx>,
    diagnostics_for: HashMap<DefId, Vec<DiagnosticBuilder<'compilation>>>,
    known_names_cache: KnownNamesCache,
    substs_cache: HashMap<DefId, SubstsRef<'tcx>>,
    // Functions to include in analysis. If None, all functions are included.
    function_whitelist: Option<Vec<String>>,
}

impl MiraiCallbacks {
    /// Analyze the crate currently being compiled, using the information given in compiler and tcx.
    #[logfn(TRACE)]
    fn analyze_with_mirai<'tcx>(&mut self, compiler: &interface::Compiler, tcx: TyCtxt<'tcx>) {
        if self.file_name.contains("crypto/crypto-derive/src")
            || self.file_name.contains("threshold_crypto")
            || self.file_name.contains("network/memsocket/src")
            || self.file_name.contains("crypto/crypto/src")
            || self.file_name.contains("common/futures-semaphore/src")
            || self.file_name.contains("common/logger/src")
            || self.file_name.contains("network/noise/src")
            || self.file_name.contains("storage/schemadb/src")
            || self.file_name.contains("network/src")
            || self.file_name.contains("types/src")
            || self.file_name.contains("language/vm/src")
            || self.file_name.contains("config/src")
            || self.file_name.contains("storage/jellyfish-merkle/src")
            || self.file_name.contains("client/libra_wallet/src")
            || self.file_name.contains("common/debug-interface/src")
            || self
                .file_name
                .contains("admission_control/admission-control-proto/src")
            || self.file_name.contains("storage/libradb/src")
            || self.file_name.contains("language/bytecode-verifier/src")
            || self.file_name.contains("executor/src")
            || self
                .file_name
                .contains("language/compiler/ir-to-bytecode/src")
            || self.file_name.contains("state-synchronizer/src")
            || self.file_name.contains("mempool/src")
            || self.file_name.contains("consensus/src")
            || self.file_name.contains("client/src")
            || self.file_name.contains("language/tools/vm-genesis/src")
            || self.file_name.contains("storage/storage-client/src")
            || self.file_name.contains("storage/scratchpad/src")
        {
            return;
        }
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
        let options = std::mem::take(&mut self.options);
        let persistent_summary_cache = PersistentSummaryCache::new(tcx, summary_store_path);
        let defs = Vec::from_iter(tcx.body_owners());
        let constant_value_cache = ConstantValueCache::default();
        let diagnostics_for: HashMap<DefId, Vec<DiagnosticBuilder<'_>>> = HashMap::new();
        let known_names_cache = KnownNamesCache::create_cache_from_language_items();
        let substs_cache = HashMap::new();
        let mut analysis_info = AnalysisInfo {
            options: &options,
            persistent_summary_cache,
            constant_value_cache,
            diagnostics_for,
            known_names_cache,
            substs_cache,
            function_whitelist: None,
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
        // Determine the functions we want to analyze.
        if let Some(fname) = &analysis_info.options.single_func {
            analysis_info.function_whitelist = Some(vec![fname.clone()]);
        } else if analysis_info.options.test_only {
            // Extract test functions from the main test runner.
            if let Some((entry_def_id, _)) = tcx.entry_fn(LOCAL_CRATE) {
                let fns = Self::extract_test_fns(tcx, entry_def_id);
                if fns.is_empty() {
                    early_error(
                        ErrorOutputType::default(),
                        "Could not extract any tests from main entry point",
                    );
                }
                info!("analyzing functions: {:?}", fns);
                analysis_info.function_whitelist = Some(fns);
            } else {
                warn!("Did not find main entry point to identify tests",);
                return;
            }
        }

        // Analyze all functions that are white listed or public
        let building_standard_summaries = std::env::var("MIRAI_START_FRESH").is_ok();
        for def_id in defs.iter() {
            let name = analysis_info
                .persistent_summary_cache
                .get_summary_key_for(*def_id);
            if let Some(white_list) = &analysis_info.function_whitelist {
                if !Self::included_in(white_list, name, *def_id, tcx) {
                    info!(
                        "skipping function {} as it is not selected for analysis",
                        name
                    );
                    continue;
                }
                info!("analyzing function {}", name);
            } else if !utils::is_public(*def_id, tcx) {
                info!("skipping function {} as it is not public", name);
                continue;
            } else if !building_standard_summaries
                && tcx.generics_of(*def_id).requires_monomorphization(tcx)
            {
                info!("skipping function {} as it is generic", name);
                continue;
            } else {
                info!("analyzing function {}", name);
            }
            MiraiCallbacks::analyze_body(compiler, tcx, analysis_info, *def_id);
        }
    }

    // Determine whether this function is included in the analysis.
    #[logfn(TRACE)]
    fn included_in(list: &[String], name: &Rc<String>, def_id: DefId, tcx: TyCtxt<'_>) -> bool {
        let display_name = utils::def_id_display_name(tcx, def_id);
        // We check both for display name and summary key name.
        list.contains(&display_name) || list.contains(name.as_ref())
    }

    /// Analyze the given function body.
    #[logfn(TRACE)]
    fn analyze_body<'analysis, 'tcx>(
        compiler: &'analysis interface::Compiler,
        tcx: TyCtxt<'tcx>,
        analysis_info: &mut AnalysisInfo<'analysis, 'tcx>,
        def_id: DefId,
    ) {
        // No need to analyze a body for which we already have a non default summary.
        // We do, however, have to allow local foreign contract functions to override
        // the standard summaries that are already in the cache.
        if !utils::is_foreign_contract(tcx, def_id) {
            let summary = analysis_info
                .persistent_summary_cache
                .get_summary_for(def_id);
            if summary.is_not_default {
                return;
            }
        }

        let mut buffered_diagnostics: Vec<DiagnosticBuilder<'_>> = vec![];
        Self::visit_body(
            def_id,
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

    /// Run the abstract interpreter over the function body and produce a summary of its effects
    /// and collect any diagnostics into the buffer.
    #[logfn(TRACE)]
    fn visit_body<'analysis, 'compilation, 'tcx>(
        def_id: DefId,
        compiler: &'compilation interface::Compiler,
        tcx: TyCtxt<'tcx>,
        analysis_info: &'analysis mut AnalysisInfo<'compilation, 'tcx>,
        mut buffered_diagnostics: &'analysis mut Vec<DiagnosticBuilder<'compilation>>,
    ) {
        let mir = tcx.optimized_mir(def_id).unwrap_read_only();
        let mut smt_solver = Z3Solver::default();
        analysis_info.constant_value_cache.reset_heap_counter();
        let mut mir_visitor = MirVisitor::new(MirVisitorCrateContext {
            options: analysis_info.options,
            session: compiler.session(),
            tcx,
            def_id,
            mir,
            summary_cache: &mut analysis_info.persistent_summary_cache,
            constant_value_cache: &mut analysis_info.constant_value_cache,
            known_names_cache: &mut analysis_info.known_names_cache,
            smt_solver: &mut smt_solver,
            substs_cache: &mut analysis_info.substs_cache,
            buffered_diagnostics: &mut buffered_diagnostics,
        });
        mir_visitor.visit_body(&[]);
    }

    /// Extract test functions from the promoted constants of a test runner main function.
    ///
    /// Currently, the #[test] attribute generates code like this:
    ///  
    ///     extern crate test;
    ///
    ///     pub fn main() -> () {
    ///       test::test_main_static(&[&test, ...)...])
    ///     }
    ///
    ///     pub const test: test:TestDescAndFn = TestDecAndFn{
    ///       ...,
    ///       testfn: test::StaticTestFn(|| test::assert_test_result(test())
    ///     };
    ///
    ///     pub fn test() { <original user test code> }
    ///  
    /// We can thus find the names (but not def def_id's) of the test functions in the main
    /// method (via const test in the example). However, the constant slice in main will be promoted
    /// into a constant initializer function in MIR, so we need to look there.
    /// We therefore iterate overall promoted functions belonging to the main function, looking for
    /// a statement like `_n = const <test name>` which loads the constant for a given test.
    ///
    /// This method is indeed not very stable and may break on changes to the compilation
    /// scheme or the test framework.
    fn extract_test_fns(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<String> {
        let mut result = vec![];
        for body in tcx.promoted_mir(def_id).iter() {
            for b in body.basic_blocks().iter() {
                for s in &b.statements {
                    // The statement we are looking for has the form
                    // `Assign(_, Rvalue(Constant(Unevaluated(def_id)))))`
                    if let mir::StatementKind::Assign(box (
                        _,
                        mir::Rvalue::Use(mir::Operand::Constant(box ref con)),
                    )) = s.kind
                    {
                        if let rustc::ty::ConstKind::Unevaluated(def_id, _, _) = con.literal.val {
                            result.push(utils::def_id_display_name(tcx, def_id));
                        }
                    }
                }
            }
        }
        result
    }
}
