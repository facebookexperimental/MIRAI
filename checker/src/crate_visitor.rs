// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// 'compilation is the lifetime of compiler interface object supplied to the after_analysis call back.
// 'tcx is the lifetime of the type context created during the lifetime of the after_analysis call back.
// 'analysis is the life time of the analyze_with_mirai call back that is invoked with the type context.

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter, Result};
use std::ops::Deref;
use std::rc::Rc;
use std::time::Instant;

use log::*;
use log_derive::{logfn, logfn_inputs};

use mirai_annotations::*;
use rustc_errors::{Diagnostic, DiagnosticBuilder};
use rustc_hir::def_id::{DefId, DefIndex};
use rustc_middle::mir;
use rustc_middle::ty::subst::SubstsRef;
use rustc_middle::ty::{TyCtxt, UnevaluatedConst};
use rustc_session::Session;

use crate::body_visitor::BodyVisitor;
use crate::call_graph::CallGraph;
use crate::constant_domain::ConstantValueCache;
use crate::expected_errors;
use crate::known_names::KnownNamesCache;
use crate::options::Options;
use crate::summaries::PersistentSummaryCache;
use crate::tag_domain::Tag;
use crate::type_visitor::TypeCache;
use crate::utils;

/// A visitor that takes information gathered by the Rust compiler when compiling a particular
/// crate and then analyses some of the functions in that crate to see if any of the assertions
/// and implicit assertions in the MIR bodies might be false and generates warning for those.
///
// 'compilation is the lifetime of the call to MiraiCallbacks::after_analysis.
// 'tcx is the lifetime of the closure call that calls analyze_with_mirai, which calls analyze_some_bodies.
pub struct CrateVisitor<'compilation, 'tcx> {
    pub buffered_diagnostics: Vec<DiagnosticBuilder<'compilation, ()>>,
    pub constant_time_tag_cache: Option<Tag>,
    pub constant_time_tag_not_found: bool,
    pub constant_value_cache: ConstantValueCache<'tcx>,
    pub diagnostics_for: HashMap<DefId, Vec<DiagnosticBuilder<'compilation, ()>>>,
    pub file_name: &'compilation str,
    pub known_names_cache: KnownNamesCache,
    pub options: &'compilation Options,
    pub session: &'compilation Session,
    pub substs_cache: HashMap<DefId, SubstsRef<'tcx>>,
    pub summary_cache: PersistentSummaryCache<'tcx>,
    pub tcx: TyCtxt<'tcx>,
    pub type_cache: Rc<RefCell<TypeCache<'tcx>>>,
    pub test_run: bool,
    pub call_graph: CallGraph<'tcx>,
}

impl<'compilation, 'tcx> Debug for CrateVisitor<'compilation, 'tcx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "CrateVisitor".fmt(f)
    }
}

impl<'compilation, 'tcx> CrateVisitor<'compilation, 'tcx> {
    /// Analyze some of the bodies in the crate that is being compiled.
    #[logfn(TRACE)]
    pub fn analyze_some_bodies(&mut self) {
        let start_instant = Instant::now();
        // Determine the functions we want to analyze.
        let selected_functions = self.get_selected_function_list();

        // Get the entry function
        let entry_fn_def_id = if let Some((def_id, _)) = self.tcx.entry_fn(()) {
            def_id
        } else {
            DefId::local(DefIndex::from_u32(0))
        };

        // Analyze all functions that are white listed or public
        let building_standard_summaries = std::env::var("MIRAI_START_FRESH").is_ok();
        for local_def_id in self.tcx.hir().body_owners() {
            let def_id = local_def_id.to_def_id();
            let name = utils::summary_key_str(self.tcx, def_id);
            if let Some(selections) = &selected_functions {
                if !self.included_in(selections.as_ref(), name.as_ref(), def_id) {
                    if self.options.single_func.is_none() {
                        debug!(
                            "skipping function {} as it is not selected for analysis",
                            name
                        );
                    }
                    continue;
                }
                info!("analyzing selected function {}", name);
            } else if !building_standard_summaries {
                if !utils::is_public(def_id, self.tcx) && def_id != entry_fn_def_id {
                    debug!("skipping function {} as it is not public", name);
                    continue;
                } else if self
                    .tcx
                    .generics_of(def_id)
                    .requires_monomorphization(self.tcx)
                {
                    debug!("skipping function {} as it is generic", name);
                    continue;
                } else if self.tcx.is_const_fn_raw(def_id) {
                    debug!("skipping function {} as it is a constant function", name);
                    continue;
                } else if utils::is_higher_order_function(def_id, self.tcx) {
                    debug!(
                        "skipping function {} as it is a higher order function",
                        name
                    );
                    continue;
                } else {
                    info!("analyzing function {}", name);
                }
            } else {
                info!("analyzing function {}", name);
            }
            self.call_graph.add_croot(def_id);
            self.analyze_body(def_id);
            if start_instant.elapsed().as_secs() > self.options.max_analysis_time_for_crate {
                info!("exceeded total time allowed for crate analysis");
                break;
            }
        }
        self.emit_or_check_diagnostics();
    }

    /// Use compilation options to determine a list of functions to analyze.
    /// If this returns None, default logic is used by the caller.
    #[logfn(TRACE)]
    fn get_selected_function_list(&mut self) -> Option<Vec<String>> {
        if let Some(func_name) = &self.options.single_func {
            Some(vec![func_name.clone()])
        } else if self.options.test_only {
            // Extract test functions from the main test runner.
            if let Some((entry_def_id, _)) = self.tcx.entry_fn(()) {
                let fns = self.extract_test_fns(entry_def_id);
                if fns.is_empty() {
                    info!("Could not extract any tests from main entry point");
                } else {
                    info!("analyzing functions: {:?}", fns);
                }
                Some(fns)
            } else {
                warn!("Did not find main entry point to identify tests",);
                None
            }
        } else {
            None
        }
    }

    // Determine whether this function is included in the analysis.
    #[logfn(TRACE)]
    fn included_in(&self, list: &[String], name: &str, def_id: DefId) -> bool {
        let display_name = utils::def_id_display_name(self.tcx, def_id);
        // We check both for display name and summary key name.
        list.iter()
            .map(|e| e.as_str())
            .any(|e| e.eq(&display_name) || e.eq(name))
    }

    /// Run the abstract interpreter over the function body and produce a summary of its effects
    /// and collect any diagnostics into the buffer.
    #[logfn(TRACE)]
    fn analyze_body(&mut self, def_id: DefId) {
        let mut diagnostics: Vec<DiagnosticBuilder<'compilation, ()>> = Vec::new();
        let mut active_calls_map: HashMap<DefId, u64> = HashMap::new();
        let mut body_visitor = BodyVisitor::new(
            self,
            def_id,
            &mut diagnostics,
            &mut active_calls_map,
            self.type_cache.clone(),
        );
        // Analysis local foreign contracts are not summarized and cached on demand, so we need to do it here.
        let summary = body_visitor.visit_body(&[]);
        let kind = self.tcx.def_kind(def_id);
        if matches!(kind, rustc_hir::def::DefKind::Static(..))
            || utils::is_foreign_contract(self.tcx, def_id)
        {
            self.summary_cache.set_summary_for(def_id, summary);
        }
        let old_diags = self.diagnostics_for.insert(def_id, diagnostics);
        checked_assume!(old_diags.is_none());
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
    fn extract_test_fns(&self, def_id: DefId) -> Vec<String> {
        let mut result = vec![];
        for body in self.tcx.promoted_mir(def_id).iter() {
            for b in body.basic_blocks.iter() {
                for s in &b.statements {
                    // The statement we are looking for has the form
                    // `Assign(_, Rvalue(Constant(UnevaluatedConst(def_id)))))`
                    if let mir::StatementKind::Assign(box (
                        _,
                        mir::Rvalue::Use(mir::Operand::Constant(box ref con)),
                    )) = s.kind
                    {
                        if let mir::ConstantKind::Ty(c) = con.literal {
                            if let rustc_middle::ty::ConstKind::Unevaluated(UnevaluatedConst {
                                def: def_ty,
                                ..
                            }) = c.kind()
                            {
                                result.push(utils::def_id_display_name(
                                    self.tcx,
                                    def_ty.def_id_for_type_of(),
                                ));
                            }
                        }
                    }
                }
            }
        }
        result
    }

    /// Emit any diagnostics or, if testing, check that they are as expected.
    #[logfn_inputs(TRACE)]
    fn emit_or_check_diagnostics(&mut self) {
        self.session.diagnostic().reset_err_count();
        if self.options.statistics {
            let num_diags = self.diagnostics_for.values().flatten().count();
            for (_, diags) in self.diagnostics_for.drain() {
                for db in diags.into_iter() {
                    db.cancel();
                }
            }
            print!("{}, analyzed, {}", self.file_name, num_diags);
        } else if self.test_run {
            let mut expected_errors = expected_errors::ExpectedErrors::new(self.file_name);
            let mut diags = vec![];
            for (_, dbs) in self.diagnostics_for.drain() {
                for db in dbs.into_iter() {
                    db.buffer(&mut diags);
                }
            }
            if !expected_errors.check_messages(diags) {
                self.session
                    .fatal(format!("test failed: {}", self.file_name));
            }
        } else {
            let mut diagnostics: Vec<&mut DiagnosticBuilder<'_, ()>> =
                self.diagnostics_for.values_mut().flatten().collect();
            fn compare_diagnostics<'a>(
                x: &&mut DiagnosticBuilder<'a, ()>,
                y: &&mut DiagnosticBuilder<'a, ()>,
            ) -> Ordering {
                let xd: &Diagnostic = x.deref();
                let yd: &Diagnostic = y.deref();
                if xd.span.primary_spans().lt(yd.span.primary_spans()) {
                    Ordering::Less
                } else if xd.span.primary_spans().gt(yd.span.primary_spans()) {
                    Ordering::Greater
                } else {
                    Ordering::Equal
                }
            }
            diagnostics.sort_by(compare_diagnostics);
            fn emit(db: &mut DiagnosticBuilder<'_, ()>) {
                db.emit();
            }
            diagnostics.into_iter().for_each(emit);
        }
    }
}
