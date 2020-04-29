// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use log_derive::*;
use mirai_annotations::*;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty::subst::SubstsRef;
use rustc_middle::ty::{Ty, TyKind};
use std::collections::HashMap;
use std::fmt::{Debug, Formatter, Result};
use std::rc::Rc;
use std::time::Instant;

use crate::abstract_value::{AbstractValue, AbstractValueTrait};
use crate::block_visitor::BlockVisitor;
use crate::body_visitor::BodyVisitor;
use crate::constant_domain::{ConstantDomain, FunctionReference};
use crate::environment::Environment;
use crate::expression::{Expression, ExpressionType, LayoutSource};
use crate::k_limits;
use crate::known_names::KnownNames;
use crate::options::DiagLevel;
use crate::path::{Path, PathEnum, PathRefinement, PathSelector};
use crate::smt_solver::SmtResult;
use crate::summaries::{Precondition, Summary};
use crate::{abstract_value, type_visitor, utils};

pub struct CallVisitor<'call, 'block, 'analysis, 'compilation, 'tcx, E> {
    pub block_visitor: &'call mut BlockVisitor<'block, 'analysis, 'compilation, 'tcx, E>,
    pub callee_def_id: DefId,
    pub callee_func_ref: Option<Rc<FunctionReference>>,
    pub callee_fun_val: Rc<AbstractValue>,
    pub callee_generic_arguments: Option<SubstsRef<'tcx>>,
    pub callee_known_name: KnownNames,
    pub callee_generic_argument_map: Option<HashMap<rustc_span::Symbol, Ty<'tcx>>>,
    pub actual_args: &'call [(Rc<Path>, Rc<AbstractValue>)],
    pub actual_argument_types: &'call [Ty<'tcx>],
    pub cleanup: Option<mir::BasicBlock>,
    pub destination: Option<(mir::Place<'tcx>, mir::BasicBlock)>,
    pub function_constant_args: &'call [(Rc<Path>, Rc<AbstractValue>)],
}

impl<'call, 'block, 'analysis, 'compilation, 'tcx, E> Debug
    for CallVisitor<'call, 'block, 'analysis, 'compilation, 'tcx, E>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "CallVisitor".fmt(f)
    }
}

impl<'call, 'block, 'analysis, 'compilation, 'tcx, E>
    CallVisitor<'call, 'block, 'analysis, 'compilation, 'tcx, E>
{
    pub(crate) fn new(
        block_visitor: &'call mut BlockVisitor<'block, 'analysis, 'compilation, 'tcx, E>,
        callee_def_id: DefId,
        callee_generic_arguments: Option<SubstsRef<'tcx>>,
        callee_generic_argument_map: Option<HashMap<rustc_span::Symbol, Ty<'tcx>>>,
        func_const: ConstantDomain,
    ) -> CallVisitor<'call, 'block, 'analysis, 'compilation, 'tcx, E> {
        if let ConstantDomain::Function(func_ref) = &func_const {
            let callee_known_name = func_ref.known_name;
            CallVisitor {
                block_visitor,
                callee_def_id,
                callee_func_ref: Some(func_ref.clone()),
                callee_fun_val: Rc::new(func_const.into()),
                callee_generic_arguments,
                callee_known_name,
                callee_generic_argument_map,
                actual_args: &[],
                actual_argument_types: &[],
                cleanup: None,
                destination: None,
                function_constant_args: &[],
            }
        } else {
            unreachable!("caller should supply a constant function")
        }
    }

    /// Summarize the referenced function, specialized by its generic arguments and the actual
    /// values of any function parameters. Then cache it.
    #[logfn_inputs(TRACE)]
    pub fn create_and_cache_function_summary(&mut self) -> Summary {
        trace!(
            "summarizing {:?}: {:?}",
            self.callee_def_id,
            self.block_visitor.bv.tcx.type_of(self.callee_def_id)
        );
        if self
            .block_visitor
            .bv
            .tcx
            .is_mir_available(self.callee_def_id)
        {
            let mut body_visitor = BodyVisitor::new(
                self.block_visitor.bv.cv,
                self.callee_def_id,
                self.block_visitor.bv.smt_solver,
                self.block_visitor.bv.buffered_diagnostics,
                self.block_visitor.bv.active_calls,
            );
            body_visitor.type_visitor.actual_argument_types = self.actual_argument_types.into();
            body_visitor.type_visitor.generic_arguments = self.callee_generic_arguments;
            body_visitor.type_visitor.generic_argument_map =
                self.callee_generic_argument_map.clone();
            let elapsed_time = self.block_visitor.bv.start_instant.elapsed();
            let summary =
                body_visitor.visit_body(self.function_constant_args, self.actual_argument_types);
            let call_was_angelic = body_visitor.assume_function_is_angelic;
            trace!(
                "summary {:?} {:?}",
                self.block_visitor.bv.function_name,
                summary
            );
            let signature = self.get_function_constant_signature(self.function_constant_args);
            if let Some(func_ref) = &self.callee_func_ref {
                // We cache the summary with call site details included so that
                // cached summaries are specialized with respect to call site generic arguments and
                // function constants arguments. Subsequent calls with the call site signature
                // will not need to re-summarize the function, thus avoiding exponential blow up.
                self.block_visitor
                    .bv
                    .cv
                    .summary_cache
                    .set_summary_for_call_site(func_ref, signature, summary.clone());
            }
            self.block_visitor.bv.assume_function_is_angelic |= call_was_angelic;
            self.block_visitor.bv.start_instant = Instant::now() - elapsed_time;
            return summary;
        } else if let Some(devirtualized_summary) = self.try_to_devirtualize() {
            return devirtualized_summary;
        }
        Summary::default()
    }

    /// If self.callee_def_id is a trait (virtual) then this tries to get the def_id of the
    /// concrete method that implements the given virtual method and returns the summary of that,
    /// computing it if necessary.
    #[logfn_inputs(TRACE)]
    fn try_to_devirtualize(&mut self) -> Option<Summary> {
        if let Some(gen_args) = self.callee_generic_arguments {
            if !utils::are_concrete(gen_args) {
                trace!("non concrete generic args {:?}", gen_args);
                return None;
            }
            // The parameter environment of the caller provides a resolution context for the callee.
            let param_env = self.block_visitor.bv.type_visitor.get_param_env();
            trace!(
                "devirtualize resolving def_id {:?}: {:?}",
                self.callee_def_id,
                self.block_visitor.bv.tcx.type_of(self.callee_def_id)
            );
            trace!("devirtualize resolving func_ref {:?}", self.callee_func_ref,);
            trace!("gen_args {:?}", gen_args);
            if let Ok(Some(instance)) = rustc_middle::ty::Instance::resolve(
                self.block_visitor.bv.tcx,
                param_env,
                self.callee_def_id,
                gen_args,
            ) {
                let resolved_def_id = instance.def.def_id();
                let resolved_ty = self.block_visitor.bv.tcx.type_of(resolved_def_id);
                trace!(
                    "devirtualize resolved def_id {:?}: {:?}",
                    resolved_def_id,
                    resolved_ty
                );
                if !self
                    .block_visitor
                    .bv
                    .active_calls
                    .contains(&resolved_def_id)
                    && self.block_visitor.bv.tcx.is_mir_available(resolved_def_id)
                {
                    let func_const = self
                        .visit_function_reference(resolved_def_id, resolved_ty, instance.substs)
                        .clone();
                    let func_ref = if let ConstantDomain::Function(fr) = &func_const {
                        fr.clone()
                    } else {
                        unreachable!()
                    };
                    let cached_summary = self
                        .block_visitor
                        .bv
                        .cv
                        .summary_cache
                        .get_summary_for_call_site(&func_ref, None);
                    if cached_summary.is_computed {
                        return Some(cached_summary.clone());
                    }

                    let generic_argument_map = self
                        .block_visitor
                        .bv
                        .type_visitor
                        .get_generic_arguments_map(
                            resolved_def_id,
                            instance.substs,
                            self.actual_argument_types,
                        );
                    let mut devirtualized_call_visitor = CallVisitor::new(
                        self.block_visitor,
                        resolved_def_id,
                        Some(instance.substs),
                        generic_argument_map,
                        func_const,
                    );
                    return Some(devirtualized_call_visitor.create_and_cache_function_summary());
                } else {
                    return None;
                }
            }
        }
        None
    }

    /// The anonymous type of a function declaration/definition. Each
    /// function has a unique type, which is output (for a function
    /// named `foo` returning an `i32`) as `fn() -> i32 {foo}`.
    ///
    /// For example the type of `bar` here:
    ///
    /// ```rust
    /// fn foo() -> i32 { 1 }
    /// let bar = foo; // bar: fn() -> i32 {foo}
    /// ```
    #[logfn_inputs(TRACE)]
    fn visit_function_reference(
        &mut self,
        def_id: DefId,
        ty: Ty<'tcx>,
        generic_args: SubstsRef<'tcx>,
    ) -> &ConstantDomain {
        self.block_visitor
            .bv
            .cv
            .substs_cache
            .insert(def_id, generic_args);
        &mut self
            .block_visitor
            .bv
            .cv
            .constant_value_cache
            .get_function_constant_for(
                def_id,
                ty,
                generic_args,
                self.block_visitor.bv.tcx,
                &mut self.block_visitor.bv.cv.known_names_cache,
                &mut self.block_visitor.bv.cv.summary_cache,
            )
    }

    /// Extract a list of function references from an environment of function constant arguments
    #[logfn_inputs(TRACE)]
    fn get_function_constant_signature(
        &mut self,
        func_args: &[(Rc<Path>, Rc<AbstractValue>)],
    ) -> Option<Vec<Rc<FunctionReference>>> {
        if func_args.is_empty() {
            return None;
        }
        let vec: Vec<Rc<FunctionReference>> = func_args
            .iter()
            .filter_map(|(_, v)| self.get_func_ref(v))
            .collect();
        if vec.is_empty() {
            return None;
        }
        Some(vec)
    }

    /// Returns the function reference part of the value, if there is one.
    #[logfn_inputs(TRACE)]
    fn get_func_ref(&mut self, val: &Rc<AbstractValue>) -> Option<Rc<FunctionReference>> {
        let extract_func_ref = |c: &ConstantDomain| match c {
            ConstantDomain::Function(func_ref) => Some(func_ref.clone()),
            _ => None,
        };
        match &val.expression {
            Expression::CompileTimeConstant(c) => {
                return extract_func_ref(c);
            }
            Expression::Reference(path)
            | Expression::Variable {
                path,
                var_type: ExpressionType::NonPrimitive,
            }
            | Expression::Variable {
                path,
                var_type: ExpressionType::Reference,
            } => {
                let closure_ty = self
                    .block_visitor
                    .bv
                    .type_visitor
                    .get_path_rustc_type(path, self.block_visitor.bv.current_span);
                match closure_ty.kind {
                    TyKind::Closure(def_id, substs) => {
                        let specialized_substs =
                            self.block_visitor.bv.type_visitor.specialize_substs(
                                substs,
                                &self.block_visitor.bv.type_visitor.generic_argument_map,
                            );
                        return extract_func_ref(self.visit_function_reference(
                            def_id,
                            closure_ty,
                            specialized_substs,
                        ));
                    }
                    TyKind::Ref(_, ty, _) => {
                        if let TyKind::Closure(def_id, substs) = ty.kind {
                            let specialized_substs =
                                self.block_visitor.bv.type_visitor.specialize_substs(
                                    substs,
                                    &self.block_visitor.bv.type_visitor.generic_argument_map,
                                );
                            return extract_func_ref(self.visit_function_reference(
                                def_id,
                                ty,
                                specialized_substs,
                            ));
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
        None
    }

    /// Returns a summary of the function to call, obtained from the summary cache.
    #[logfn_inputs(TRACE)]
    pub fn get_function_summary(&mut self) -> Option<Summary> {
        let fun_val = self.callee_fun_val.clone();
        if let Some(func_ref) = self.get_func_ref(&fun_val) {
            // If the actual arguments include any function constants, collect them together
            // and pass them to get_summary_for_function_constant so that their signatures
            // can be included in the type specific key that is used to look up non generic
            // predefined summaries.
            let func_args: Option<Vec<Rc<FunctionReference>>> =
                if !self.function_constant_args.is_empty() {
                    Some(
                        self.function_constant_args
                            .iter()
                            .filter_map(|(_, v)| self.get_func_ref(v))
                            .collect(),
                    )
                } else {
                    // common case
                    None
                };
            let result = self
                .block_visitor
                .bv
                .cv
                .summary_cache
                .get_summary_for_call_site(&func_ref, func_args)
                .clone();
            if result.is_computed || func_ref.def_id.is_none() {
                return Some(result);
            }
            if !self
                .block_visitor
                .bv
                .active_calls
                .contains(&func_ref.def_id.unwrap())
            {
                return Some(self.create_and_cache_function_summary());
            }
        }
        None
    }

    /// If the current call is to a well known function for which we don't have a cached summary,
    /// this function will update the environment as appropriate and return true. If the return
    /// result is false, just carry on with the normal logic.
    #[logfn_inputs(TRACE)]
    pub fn handled_as_special_function_call(&mut self) -> bool {
        match self.callee_known_name {
            KnownNames::StdOpsFunctionFnCall
            | KnownNames::StdOpsFunctionFnMutCallMut
            | KnownNames::StdOpsFunctionFnOnceCallOnce => {
                self.inline_indirectly_called_function();
                return true;
            }
            KnownNames::MiraiAbstractValue => {
                checked_assume!(self.actual_args.len() == 1);
                self.handle_abstract_value();
                return true;
            }
            KnownNames::MiraiAssume => {
                checked_assume!(self.actual_args.len() == 1);
                if self.block_visitor.bv.check_for_errors {
                    self.report_calls_to_special_functions();
                }
                self.handle_assume();
                return true;
            }
            KnownNames::MiraiAssumePreconditions => {
                checked_assume!(self.actual_args.is_empty());
                self.block_visitor.bv.assume_preconditions_of_next_call = true;
                return true;
            }
            KnownNames::MiraiGetModelField => {
                self.handle_get_model_field();
                return true;
            }
            KnownNames::MiraiPostcondition => {
                checked_assume!(self.actual_args.len() == 3);
                if self.block_visitor.bv.check_for_errors {
                    self.report_calls_to_special_functions();
                }
                self.handle_post_condition();
                return true;
            }
            KnownNames::MiraiPreconditionStart => {
                self.handle_precondition_start();
                return true;
            }
            KnownNames::MiraiPrecondition => {
                checked_assume!(self.actual_args.len() == 2);
                self.handle_precondition();
                self.handle_assume();
                return true;
            }
            KnownNames::MiraiSetModelField => {
                self.handle_set_model_field();
                return true;
            }
            KnownNames::MiraiShallowClone => {
                if let Some((place, target)) = &self.destination {
                    checked_assume!(self.actual_args.len() == 1);
                    let source_path = self.actual_args[0].0.clone();
                    let target_type = self
                        .block_visitor
                        .bv
                        .type_visitor
                        .get_rustc_place_type(place, self.block_visitor.bv.current_span);
                    let target_path = self.block_visitor.visit_place(place);
                    self.block_visitor.copy_or_move_elements(
                        target_path,
                        source_path,
                        target_type,
                        false,
                    );
                    let exit_condition = self
                        .block_visitor
                        .bv
                        .current_environment
                        .entry_condition
                        .clone();
                    self.block_visitor.bv.current_environment.exit_conditions = self
                        .block_visitor
                        .bv
                        .current_environment
                        .exit_conditions
                        .insert(*target, exit_condition);
                } else {
                    assume_unreachable!();
                }
                return true;
            }
            KnownNames::MiraiResult => {
                if let Some((place, target)) = &self.destination {
                    let target_path = self.block_visitor.visit_place(place);
                    let target_rustc_type = self
                        .block_visitor
                        .bv
                        .type_visitor
                        .get_rustc_place_type(place, self.block_visitor.bv.current_span);
                    let return_value_path = Path::new_result();
                    let return_value = self
                        .block_visitor
                        .bv
                        .lookup_path_and_refine_result(return_value_path, target_rustc_type);
                    self.block_visitor
                        .bv
                        .current_environment
                        .update_value_at(target_path, return_value);
                    let exit_condition = self
                        .block_visitor
                        .bv
                        .current_environment
                        .entry_condition
                        .clone();
                    self.block_visitor.bv.current_environment.exit_conditions = self
                        .block_visitor
                        .bv
                        .current_environment
                        .exit_conditions
                        .insert(*target, exit_condition);
                } else {
                    assume_unreachable!();
                }
                return true;
            }
            KnownNames::MiraiVerify => {
                checked_assume!(self.actual_args.len() == 2);
                if self.block_visitor.bv.check_for_errors {
                    self.report_calls_to_special_functions();
                }
                self.actual_args = &self.actual_args[0..1];
                self.handle_assume();
                return true;
            }
            KnownNames::RustDealloc => {
                self.handle_rust_dealloc();
                if let Some((_, target)) = &self.destination {
                    let exit_condition = self
                        .block_visitor
                        .bv
                        .current_environment
                        .entry_condition
                        .clone();
                    self.block_visitor.bv.current_environment.exit_conditions = self
                        .block_visitor
                        .bv
                        .current_environment
                        .exit_conditions
                        .insert(*target, exit_condition);
                } else {
                    assume_unreachable!("a call to __rust_dealloc should have a target block");
                }
                return true;
            }
            KnownNames::StdFutureFromGenerator => {
                checked_assume!(self.actual_args.len() == 1);
                let generator_fun_val = self.actual_args[0].1.clone();
                let generator_fun_ref = self.get_func_ref(&generator_fun_val).expect("a fun ref");
                let generator_def_id = generator_fun_ref.def_id.expect("a def id");
                let mut block_visitor = BlockVisitor::<E>::new(self.block_visitor.bv);
                let mut generator_call_visitor = CallVisitor::new(
                    &mut block_visitor,
                    generator_def_id,
                    None,
                    None,
                    ConstantDomain::Function(generator_fun_ref),
                );
                self.block_visitor.bv.async_fn_summary =
                    generator_call_visitor.get_function_summary();
                return true;
            }
            KnownNames::StdIntrinsicsCopyNonOverlapping => {
                self.handle_copy_non_overlapping();
                if let Some((_, target)) = &self.destination {
                    let exit_condition = self
                        .block_visitor
                        .bv
                        .current_environment
                        .entry_condition
                        .clone();
                    self.block_visitor.bv.current_environment.exit_conditions = self
                        .block_visitor
                        .bv
                        .current_environment
                        .exit_conditions
                        .insert(*target, exit_condition);
                }
                return true;
            }
            KnownNames::StdPanickingBeginPanic | KnownNames::StdPanickingBeginPanicFmt => {
                if self.block_visitor.bv.check_for_errors {
                    self.report_calls_to_special_functions(); //known_name, actual_args);
                }
                if let Some((_, target)) = &self.destination {
                    self.block_visitor.bv.current_environment.exit_conditions = self
                        .block_visitor
                        .bv
                        .current_environment
                        .exit_conditions
                        .insert(*target, abstract_value::FALSE.into());
                }
                return true;
            }
            _ => {
                let result = self.try_to_inline_special_function();
                if !result.is_bottom() {
                    if let Some((place, target)) = &self.destination {
                        let target_path = self.block_visitor.visit_place(place);
                        self.block_visitor
                            .bv
                            .current_environment
                            .update_value_at(target_path, result);
                        let exit_condition = self
                            .block_visitor
                            .bv
                            .current_environment
                            .entry_condition
                            .clone();
                        self.block_visitor.bv.current_environment.exit_conditions = self
                            .block_visitor
                            .bv
                            .current_environment
                            .exit_conditions
                            .insert(*target, exit_condition);
                        return true;
                    }
                }
            }
        }
        false
    }

    /// If the function being called is a special function like mirai_annotations.mirai_verify or
    /// std.panicking.begin_panic then report a diagnostic or create a precondition as appropriate.
    #[logfn_inputs(TRACE)]
    fn report_calls_to_special_functions(&mut self) {
        precondition!(self.block_visitor.bv.check_for_errors);
        match self.callee_known_name {
            KnownNames::MiraiAssume => {
                assume!(self.actual_args.len() == 1);
                let (_, cond) = &self.actual_args[0];
                let (cond_as_bool, entry_cond_as_bool) = self
                    .block_visitor
                    .check_condition_value_and_reachability(cond);

                // If we never get here, rather call unreachable!()
                if !entry_cond_as_bool.unwrap_or(true) {
                    let span = self.block_visitor.bv.current_span;
                    let message =
                        "this is unreachable, mark it as such by using the unreachable! macro";
                    let warning = self
                        .block_visitor
                        .bv
                        .cv
                        .session
                        .struct_span_warn(span, message);
                    self.block_visitor.bv.emit_diagnostic(warning);
                    return;
                }

                // If the condition is always true, this assumption is redundant
                if cond_as_bool.unwrap_or(false) {
                    let span = self.block_visitor.bv.current_span;
                    let warning =
                        self.block_visitor.bv.cv.session.struct_span_warn(
                            span,
                            "assumption is provably true and can be deleted",
                        );
                    self.block_visitor.bv.emit_diagnostic(warning);
                }
            }
            KnownNames::MiraiPostcondition => {
                assume!(self.actual_args.len() == 3); // The type checker ensures this.
                let (_, assumption) = &self.actual_args[1];
                let (_, cond) = &self.actual_args[0];
                if !assumption.as_bool_if_known().unwrap_or(false) {
                    let message = self.coerce_to_string(&self.actual_args[2].1);
                    if self
                        .block_visitor
                        .check_condition(cond, message, true)
                        .is_none()
                    {
                        self.block_visitor.try_extend_post_condition(&cond);
                    }
                } else {
                    self.block_visitor.try_extend_post_condition(&cond);
                }
            }
            KnownNames::MiraiVerify => {
                assume!(self.actual_args.len() == 2); // The type checker ensures this.
                let (_, cond) = &self.actual_args[0];
                let message = self.coerce_to_string(&self.actual_args[1].1);
                if let Some(warning) = self.block_visitor.check_condition(cond, message, false) {
                    // Push a precondition so that any known or unknown caller of this function
                    // is warned that this function will fail if the precondition is not met.
                    if self.block_visitor.bv.preconditions.len()
                        < k_limits::MAX_INFERRED_PRECONDITIONS
                    {
                        let condition = self
                            .block_visitor
                            .bv
                            .current_environment
                            .entry_condition
                            .logical_not()
                            .or(cond.clone());
                        let precondition = Precondition {
                            condition,
                            message: Rc::new(warning),
                            provenance: None,
                            spans: vec![self.block_visitor.bv.current_span],
                        };
                        self.block_visitor.bv.preconditions.push(precondition);
                    }
                }
            }
            KnownNames::StdPanickingBeginPanic | KnownNames::StdPanickingBeginPanicFmt => {
                assume!(!self.actual_args.is_empty()); // The type checker ensures this.
                let mut path_cond = self
                    .block_visitor
                    .bv
                    .current_environment
                    .entry_condition
                    .as_bool_if_known();
                if path_cond.is_none() {
                    // Try the SMT solver
                    let path_expr = &self
                        .block_visitor
                        .bv
                        .current_environment
                        .entry_condition
                        .expression;
                    let path_smt = self
                        .block_visitor
                        .bv
                        .smt_solver
                        .get_as_smt_predicate(path_expr);
                    if self.block_visitor.bv.smt_solver.solve_expression(&path_smt)
                        == SmtResult::Unsatisfiable
                    {
                        path_cond = Some(false)
                    }
                }
                if !path_cond.unwrap_or(true) {
                    // We never get to this call, so nothing to report.
                    return;
                }

                let fmt_string =
                    if matches!(self.callee_known_name, KnownNames::StdPanickingBeginPanic) {
                        self.actual_args[0].1.clone()
                    } else {
                        let index = Rc::new(0u128.into());
                        let args_pieces_0 = Path::new_index(
                            Path::new_field(self.actual_args[0].0.clone(), 0),
                            index,
                        )
                        .refine_paths(&self.block_visitor.bv.current_environment);
                        self.block_visitor.bv.lookup_path_and_refine_result(
                            args_pieces_0,
                            ExpressionType::Reference.as_rustc_type(self.block_visitor.bv.tcx),
                        )
                    };
                let msg = if let Expression::CompileTimeConstant(ConstantDomain::Str(msg)) =
                    &fmt_string.expression
                {
                    if msg.contains("entered unreachable code")
                        || msg.contains("not yet implemented")
                        || msg.starts_with("unrecoverable: ")
                    {
                        // We treat unreachable!() as an assumption rather than an assertion to prove.
                        // unimplemented!() is unlikely to be a programmer mistake, so need to fixate on that either.
                        // unrecoverable! is way for the programmer to indicate that termination is not a mistake.
                        return;
                    } else {
                        if path_cond.is_none() && msg.as_str() == "statement is reachable" {
                            // verify_unreachable should always complain if possibly reachable
                            // and the current function is public or root.
                            path_cond = Some(true);
                        }
                        msg.clone()
                    }
                } else {
                    Rc::new(String::from("execution panic"))
                };
                let span = self.block_visitor.bv.current_span;

                if path_cond.unwrap_or(false) && self.function_being_analyzed_is_root() {
                    // We always get to this call and we have to assume that the function will
                    // get called, so keep the message certain.
                    // Don't, however, complain about panics in the standard contract summaries
                    if std::env::var("MIRAI_START_FRESH").is_err() {
                        let err = self
                            .block_visitor
                            .bv
                            .cv
                            .session
                            .struct_span_warn(span, msg.as_str());
                        self.block_visitor.bv.emit_diagnostic(err);
                    }
                } else {
                    // We might get to this call, depending on the state at the call site.
                    //
                    // In the case when an assert macro has been called, the inverse of the assertion
                    // was conjoined into the entry condition and this condition was simplified.
                    // We therefore cannot distinguish the case of maybe reaching a definitely
                    // false assertion from the case of definitely reaching a maybe false assertion.
                    //
                    // Since the assert and panic macros are commonly used to create preconditions
                    // it would be very inconvenient if this possibly false assertion were reported
                    // as a problem since there would be no way to shut it up. We therefore do not
                    // report this and instead insist that anyone who wants to have MIRAI check
                    // their assertions should use the mirai_annotations::verify! macro instead.
                    //
                    // We **do** have to push a precondition since this is the probable intent.
                    let condition = self
                        .block_visitor
                        .bv
                        .current_environment
                        .entry_condition
                        .logical_not();
                    let precondition = Precondition {
                        condition,
                        message: msg,
                        provenance: None,
                        spans: if self.block_visitor.bv.def_id.is_local() {
                            vec![span]
                        } else {
                            vec![] // The span is likely inside a standard macro, i.e. panic! etc.
                        },
                    };
                    self.block_visitor.bv.preconditions.push(precondition);
                }
            }
            _ => assume_unreachable!(),
        }
    }

    /// Provides special handling of functions that have no MIR bodies or that need to access
    /// internal MIRAI state in ways that cannot be expressed in normal Rust and therefore
    /// cannot be summarized in the standard_contracts crate.
    /// Returns the result of the call, or BOTTOM if the function to call is not a known
    /// special function.
    #[allow(clippy::cognitive_complexity)]
    #[logfn_inputs(TRACE)]
    fn try_to_inline_special_function(&mut self) -> Rc<AbstractValue> {
        match self.callee_known_name {
            KnownNames::RustAlloc => self.handle_rust_alloc(),
            KnownNames::RustAllocZeroed => self.handle_rust_alloc_zeroed(),
            KnownNames::RustRealloc => self.handle_rust_realloc(),
            KnownNames::StdIntrinsicsArithOffset => self.handle_arith_offset(),
            KnownNames::StdIntrinsicsBitreverse
            | KnownNames::StdIntrinsicsBswap
            | KnownNames::StdIntrinsicsCtlz
            | KnownNames::StdIntrinsicsCtpop
            | KnownNames::StdIntrinsicsCttz => {
                checked_assume!(self.actual_args.len() == 1);
                let arg_type: ExpressionType = (&self.actual_argument_types[0].kind).into();
                let bit_length = arg_type.bit_length();
                self.actual_args[0]
                    .1
                    .intrinsic_bit_vector_unary(bit_length, self.callee_known_name)
            }
            KnownNames::StdIntrinsicsCtlzNonzero | KnownNames::StdIntrinsicsCttzNonzero => {
                checked_assume!(self.actual_args.len() == 1);
                if self.block_visitor.bv.check_for_errors {
                    let non_zero = self.actual_args[0].1.not_equals(Rc::new(0u128.into()));
                    self.block_visitor.check_condition(
                        &non_zero,
                        Rc::new("argument is zero".to_owned()),
                        false,
                    );
                }
                let arg_type: ExpressionType = (&self.actual_argument_types[0].kind).into();
                let bit_length = arg_type.bit_length();
                self.actual_args[0]
                    .1
                    .intrinsic_bit_vector_unary(bit_length, self.callee_known_name)
            }
            KnownNames::StdIntrinsicsCeilf32
            | KnownNames::StdIntrinsicsCeilf64
            | KnownNames::StdIntrinsicsCosf32
            | KnownNames::StdIntrinsicsCosf64
            | KnownNames::StdIntrinsicsExp2f32
            | KnownNames::StdIntrinsicsExp2f64
            | KnownNames::StdIntrinsicsExpf32
            | KnownNames::StdIntrinsicsExpf64
            | KnownNames::StdIntrinsicsFabsf32
            | KnownNames::StdIntrinsicsFabsf64
            | KnownNames::StdIntrinsicsFloorf32
            | KnownNames::StdIntrinsicsFloorf64
            | KnownNames::StdIntrinsicsLog10f32
            | KnownNames::StdIntrinsicsLog10f64
            | KnownNames::StdIntrinsicsLog2f32
            | KnownNames::StdIntrinsicsLog2f64
            | KnownNames::StdIntrinsicsLogf32
            | KnownNames::StdIntrinsicsLogf64
            | KnownNames::StdIntrinsicsNearbyintf32
            | KnownNames::StdIntrinsicsNearbyintf64
            | KnownNames::StdIntrinsicsRintf32
            | KnownNames::StdIntrinsicsRintf64
            | KnownNames::StdIntrinsicsRoundf32
            | KnownNames::StdIntrinsicsRoundf64
            | KnownNames::StdIntrinsicsSinf32
            | KnownNames::StdIntrinsicsSinf64
            | KnownNames::StdIntrinsicsSqrtf32
            | KnownNames::StdIntrinsicsSqrtf64
            | KnownNames::StdIntrinsicsTruncf32
            | KnownNames::StdIntrinsicsTruncf64 => {
                checked_assume!(self.actual_args.len() == 1);
                self.actual_args[0]
                    .1
                    .intrinsic_floating_point_unary(self.callee_known_name)
            }
            KnownNames::StdIntrinsicsCopysignf32
            | KnownNames::StdIntrinsicsCopysignf64
            | KnownNames::StdIntrinsicsFaddFast
            | KnownNames::StdIntrinsicsFdivFast
            | KnownNames::StdIntrinsicsFmulFast
            | KnownNames::StdIntrinsicsFremFast
            | KnownNames::StdIntrinsicsFsubFast
            | KnownNames::StdIntrinsicsMaxnumf32
            | KnownNames::StdIntrinsicsMaxnumf64
            | KnownNames::StdIntrinsicsMinnumf32
            | KnownNames::StdIntrinsicsMinnumf64
            | KnownNames::StdIntrinsicsPowf32
            | KnownNames::StdIntrinsicsPowf64
            | KnownNames::StdIntrinsicsPowif32
            | KnownNames::StdIntrinsicsPowif64 => {
                checked_assume!(self.actual_args.len() == 2);
                self.actual_args[0]
                    .1
                    .intrinsic_binary(self.actual_args[1].1.clone(), self.callee_known_name)
            }
            KnownNames::StdIntrinsicsMulWithOverflow => self.handle_checked_binary_operation(),
            KnownNames::StdIntrinsicsOffset => self.handle_offset(),
            KnownNames::StdIntrinsicsTransmute => {
                checked_assume!(self.actual_args.len() == 1);
                self.actual_args[0].1.clone()
            }
            KnownNames::StdMemSizeOf => self.handle_size_of(),
            _ => abstract_value::BOTTOM.into(),
        }
    }

    /// Fn::call, FnMut::call_mut, FnOnce::call_once all receive two arguments:
    /// 1. A function pointer or closure instance to call.
    /// 2. A tuple of argument values for the call.
    /// The tuple is unpacked and the callee is then invoked with its normal function signature.
    /// In the case of calling a closure, the closure signature includes the closure as the first argument.
    ///
    /// All of this happens in code that is not encoded as MIR, so MIRAI needs built in support for it.
    #[logfn_inputs(TRACE)]
    fn inline_indirectly_called_function(&mut self) {
        checked_assume!(self.actual_args.len() == 2);
        // Get the function to call (it is either a function pointer or a closure)
        let callee = self.actual_args[0].1.clone();

        // Get the path of the tuple containing the arguments.
        let callee_arg_array_path = self.actual_args[1].0.clone();

        // Unpack the arguments. We use the generic arguments of the caller as a proxy for the callee function signature.
        let generic_argument_types: Vec<Ty<'tcx>> = self
            .callee_generic_arguments
            .expect("call_once, etc. are generic")
            .as_ref()
            .iter()
            .map(|gen_arg| gen_arg.expect_ty())
            .collect();

        checked_assume!(generic_argument_types.len() == 2);
        let mut actual_argument_types: Vec<Ty<'tcx>>;
        if let TyKind::Tuple(tuple_types) = generic_argument_types[1].kind {
            actual_argument_types = tuple_types
                .iter()
                .map(|gen_arg| gen_arg.expect_ty())
                .collect();
        } else {
            assume_unreachable!("expected second type argument to be a tuple type");
        }

        let mut actual_args: Vec<(Rc<Path>, Rc<AbstractValue>)> = actual_argument_types
            .iter()
            .enumerate()
            .map(|(i, t)| {
                let arg_path = Path::new_field(callee_arg_array_path.clone(), i)
                    .refine_paths(&self.block_visitor.bv.current_environment);
                let arg_val = self
                    .block_visitor
                    .bv
                    .lookup_path_and_refine_result(arg_path.clone(), t);
                (arg_path, arg_val)
            })
            .collect();

        // Prepend the closure (if there is one) to the unpacked arguments vector.
        // Also update the Self parameter in the arguments map.
        let mut closure_ty = self.actual_argument_types[0];
        if let TyKind::Ref(_, ty, _) = closure_ty.kind {
            closure_ty = ty;
        }
        let mut argument_map = self.callee_generic_argument_map.clone();
        if type_visitor::get_def_id_from_closure(closure_ty).is_some() {
            actual_args.insert(0, self.actual_args[0].clone());
            actual_argument_types.insert(0, closure_ty);
            if let TyKind::Closure(_, substs) = closure_ty.kind {
                let mut map = argument_map.unwrap_or_else(HashMap::new);
                if let Some(ty) = substs.types().next() {
                    let self_sym = rustc_span::Symbol::intern("Self");
                    map.insert(self_sym, ty);
                }
                argument_map = Some(map);
            }
        }

        let function_constant_args = self.get_function_constant_args(&actual_args);
        let callee_func_ref = self.get_func_ref(&callee);

        let function_summary = if let Some(func_ref) = &callee_func_ref {
            let func_const = ConstantDomain::Function(func_ref.clone());
            let def_id = func_ref.def_id.expect("defined when used here");
            let generic_arguments = self.block_visitor.bv.cv.substs_cache.get(&def_id).cloned();
            let mut block_visitor = BlockVisitor::<E>::new(self.block_visitor.bv);
            let mut indirect_call_visitor = CallVisitor::new(
                &mut block_visitor,
                def_id,
                generic_arguments,
                argument_map,
                func_const,
            );
            indirect_call_visitor.actual_args = &actual_args;
            indirect_call_visitor.actual_argument_types = &actual_argument_types;
            indirect_call_visitor.function_constant_args = &function_constant_args;
            indirect_call_visitor.callee_fun_val = callee;
            indirect_call_visitor.callee_known_name = KnownNames::None;
            indirect_call_visitor.destination = self.destination;
            let summary = indirect_call_visitor.get_function_summary();
            if let Some(summary) = summary {
                indirect_call_visitor.check_preconditions_if_necessary(&summary);
                indirect_call_visitor.transfer_and_refine_normal_return_state(&summary);
                indirect_call_visitor.transfer_and_refine_cleanup_state(&summary);
                return;
            } else {
                self.deal_with_missing_summary();
                Summary::default()
            }
        } else {
            self.deal_with_missing_summary();
            Summary::default()
        };

        self.check_preconditions_if_necessary(&function_summary);
        self.transfer_and_refine_normal_return_state(&function_summary);
        self.transfer_and_refine_cleanup_state(&function_summary);
    }

    /// Replace the call result with an abstract value of the same type as the
    /// destination place.
    #[logfn_inputs(TRACE)]
    fn handle_abstract_value(&mut self) {
        if let Some((place, target)) = &self.destination {
            let path = self.block_visitor.visit_place(place);
            let expression_type = self
                .block_visitor
                .bv
                .type_visitor
                .get_place_type(place, self.block_visitor.bv.current_span);
            let abstract_value = AbstractValue::make_from(
                Expression::Variable {
                    path: path.clone(),
                    var_type: expression_type,
                },
                1,
            );
            self.block_visitor
                .bv
                .current_environment
                .update_value_at(path, abstract_value);
            let exit_condition = self
                .block_visitor
                .bv
                .current_environment
                .entry_condition
                .clone();
            self.block_visitor.bv.current_environment.exit_conditions = self
                .block_visitor
                .bv
                .current_environment
                .exit_conditions
                .insert(*target, exit_condition);
        } else {
            assume_unreachable!();
        }
    }

    /// Adds the first and only value in actual_args to the path condition of the destination.
    /// No check is performed, since we get to assume this condition without proof.
    #[logfn_inputs(TRACE)]
    fn handle_assume(&mut self) {
        precondition!(self.actual_args.len() == 1);
        let assumed_condition = &self.actual_args[0].1;
        let exit_condition = self
            .block_visitor
            .bv
            .current_environment
            .entry_condition
            .and(assumed_condition.clone());
        if let Some((_, target)) = &self.destination {
            self.block_visitor.bv.current_environment.exit_conditions = self
                .block_visitor
                .bv
                .current_environment
                .exit_conditions
                .insert(*target, exit_condition);
        } else {
            assume_unreachable!();
        }
        if let Some(cleanup_target) = self.cleanup {
            self.block_visitor.bv.current_environment.exit_conditions = self
                .block_visitor
                .bv
                .current_environment
                .exit_conditions
                .insert(cleanup_target, abstract_value::FALSE.into());
        }
    }

    /// Update the state so that the call result is the value of the model field (or the default
    /// value if there is no field).
    #[logfn_inputs(TRACE)]
    fn handle_get_model_field(&mut self) {
        let destination = self.destination;
        if let Some((place, target)) = &destination {
            let target_type = self
                .block_visitor
                .bv
                .type_visitor
                .get_rustc_place_type(place, self.block_visitor.bv.current_span);
            checked_assume!(self.actual_args.len() == 3);

            // The current value, if any, of the model field are a set of (path, value) pairs
            // where each path is rooted by qualifier.model_field(..)
            let qualifier = self.actual_args[0].0.clone();
            let field_name = self.coerce_to_string(&self.actual_args[1].1);
            let source_path = Path::new_model_field(qualifier, field_name)
                .refine_paths(&self.block_visitor.bv.current_environment);

            let target_path = self.block_visitor.visit_place(place);
            if self
                .block_visitor
                .bv
                .current_environment
                .value_at(&source_path)
                .is_some()
            {
                // Move the model field (path, val) pairs to the target (i.e. the place where
                // the return value of call to the mirai_get_model_field function would go if
                // it were a normal call.
                self.block_visitor.copy_or_move_elements(
                    target_path,
                    source_path,
                    target_type,
                    true,
                );
            } else {
                // If there is no value for the model field in the environment, we should
                // use the default value, but only if the qualifier is not rooted in a parameter
                // value since only the caller will know what the values of the fields are.
                match &self.actual_args[0].1.expression {
                    Expression::Reference(path) | Expression::Variable { path, .. }
                        if path.is_rooted_by_parameter() =>
                    {
                        //todo: if the default value is a non primitive then we lose the structure
                        // using the code below. That is wrong. Generalize the default field.
                        let rval = AbstractValue::make_from(
                            Expression::UnknownModelField {
                                path: source_path,
                                default: self.actual_args[2].1.clone(),
                            },
                            1,
                        );
                        self.block_visitor
                            .bv
                            .current_environment
                            .update_value_at(target_path, rval);
                    }
                    _ => {
                        let source_path = self.actual_args[2].0.clone();
                        self.block_visitor.copy_or_move_elements(
                            target_path,
                            source_path,
                            target_type,
                            true,
                        );
                    }
                }
            }
            let exit_condition = self
                .block_visitor
                .bv
                .current_environment
                .entry_condition
                .clone();
            self.block_visitor.bv.current_environment.exit_conditions = self
                .block_visitor
                .bv
                .current_environment
                .exit_conditions
                .insert(*target, exit_condition);
        } else {
            assume_unreachable!();
        }
    }

    fn handle_post_condition(&mut self) {
        precondition!(self.actual_args.len() == 3);
        let condition = self.actual_args[0].1.clone();
        let exit_condition = self
            .block_visitor
            .bv
            .current_environment
            .entry_condition
            .and(condition);
        if let Some((_, target)) = &self.destination {
            self.block_visitor.bv.current_environment.exit_conditions = self
                .block_visitor
                .bv
                .current_environment
                .exit_conditions
                .insert(*target, exit_condition);
        } else {
            assume_unreachable!();
        }
    }

    /// It is bad style for a precondition to be reached conditionally, since well, that condition
    /// should be part of the precondition.
    #[logfn_inputs(TRACE)]
    fn handle_precondition_start(&mut self) {
        if self.block_visitor.bv.check_for_errors
            && self.block_visitor.bv.check_for_unconditional_precondition
            && !self
                .block_visitor
                .bv
                .current_environment
                .entry_condition
                .as_bool_if_known()
                .unwrap_or(false)
        {
            let span = self.block_visitor.bv.current_span;
            let warning = self
                .block_visitor
                .bv
                .cv
                .session
                .struct_span_warn(span, "preconditions should be reached unconditionally");
            self.block_visitor.bv.emit_diagnostic(warning);
            self.block_visitor.bv.check_for_unconditional_precondition = false;
        }
        let exit_condition = self
            .block_visitor
            .bv
            .current_environment
            .entry_condition
            .clone();
        if let Some((_, target)) = &self.destination {
            self.block_visitor.bv.current_environment.exit_conditions = self
                .block_visitor
                .bv
                .current_environment
                .exit_conditions
                .insert(*target, exit_condition);
        } else {
            assume_unreachable!();
        }
    }

    /// Adds the first and only value in actual_args to the current list of preconditions.
    /// No check is performed, since we get to assume the caller has verified this condition.
    #[logfn_inputs(TRACE)]
    fn handle_precondition(&mut self) {
        precondition!(self.actual_args.len() == 2);
        if self.block_visitor.bv.check_for_errors {
            let condition = self.actual_args[0].1.clone();
            let message = self.coerce_to_string(&self.actual_args[1].1);
            let precondition = Precondition {
                condition,
                message,
                provenance: None,
                spans: vec![self.block_visitor.bv.current_span],
            };
            self.block_visitor.bv.preconditions.push(precondition);
        }
    }

    /// Update the state to reflect the assignment of the model field.
    #[logfn_inputs(TRACE)]
    fn handle_set_model_field(&mut self) {
        checked_assume!(self.actual_args.len() == 3);
        let destination = self.destination;
        if let Some((_, target)) = &destination {
            let qualifier = self.actual_args[0].0.clone();
            let field_name = self.coerce_to_string(&self.actual_args[1].1);
            let target_path = Path::new_model_field(qualifier, field_name)
                .refine_paths(&self.block_visitor.bv.current_environment);
            let source_path = self.actual_args[2].0.clone();
            let target_type = self.actual_argument_types[2];
            self.block_visitor
                .copy_or_move_elements(target_path, source_path, target_type, true);
            let exit_condition = self
                .block_visitor
                .bv
                .current_environment
                .entry_condition
                .clone();
            self.block_visitor.bv.current_environment.exit_conditions = self
                .block_visitor
                .bv
                .current_environment
                .exit_conditions
                .insert(*target, exit_condition);
        } else {
            assume_unreachable!();
        }
    }

    /// Removes the heap block and all paths rooted in it from the current environment.
    #[logfn_inputs(TRACE)]
    fn handle_rust_dealloc(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_args.len() == 3);

        // The current environment is that that of the caller, but the caller is a standard
        // library function and has no interesting state to purge.
        // The layout path inserted below will become a side effect of the caller and when that
        // side effect is refined by the caller's caller, the refinement will do the purge if the
        // qualifier of the path is a heap block path.

        // Get path to the heap block to deallocate
        let heap_block_path = self.actual_args[0].0.clone();

        // Create a layout
        let length = self.actual_args[1].1.clone();
        let alignment = self.actual_args[2].1.clone();
        let layout = AbstractValue::make_from(
            Expression::HeapBlockLayout {
                length,
                alignment,
                source: LayoutSource::DeAlloc,
            },
            1,
        );

        // Get a layout path and update the environment
        let layout_path = Path::new_layout(heap_block_path)
            .refine_paths(&self.block_visitor.bv.current_environment);
        self.block_visitor
            .bv
            .current_environment
            .update_value_at(layout_path, layout);

        // Signal to the caller that there is no return result
        abstract_value::BOTTOM.into()
    }

    /// Copies a slice of elements from the source to the destination.
    #[logfn_inputs(TRACE)]
    fn handle_copy_non_overlapping(&mut self) {
        checked_assume!(self.actual_args.len() == 3);
        let target_root = self.actual_args[0].0.clone();
        let source_path = self.actual_args[1].0.clone();
        let count = self.actual_args[2].1.clone();
        let target_path = Path::new_slice(target_root, count)
            .refine_paths(&self.block_visitor.bv.current_environment);
        let collection_type = self.actual_argument_types[0];
        self.block_visitor
            .copy_or_move_elements(target_path, source_path, collection_type, false);
    }

    /// Returns a new heap memory block with the given byte length.
    #[logfn_inputs(TRACE)]
    fn handle_rust_alloc(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_args.len() == 2);
        let length = self.actual_args[0].1.clone();
        let alignment = self.actual_args[1].1.clone();
        let heap_path = Path::get_as_path(
            self.block_visitor
                .bv
                .get_new_heap_block(length, alignment, false),
        );
        AbstractValue::make_reference(heap_path)
    }

    /// Returns a new heap memory block with the given byte length and with the zeroed flag set.
    #[logfn_inputs(TRACE)]
    fn handle_rust_alloc_zeroed(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_args.len() == 2);
        let length = self.actual_args[0].1.clone();
        let alignment = self.actual_args[1].1.clone();
        let heap_path = Path::get_as_path(
            self.block_visitor
                .bv
                .get_new_heap_block(length, alignment, true),
        );
        AbstractValue::make_reference(heap_path)
    }

    /// Sets the length of the heap block to a new value and removes index paths as necessary
    /// if the new length is known and less than the old lengths.
    #[logfn_inputs(TRACE)]
    fn handle_rust_realloc(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_args.len() == 4);
        // Get path to the heap block to reallocate
        let heap_block_path = Path::new_deref(self.actual_args[0].0.clone());

        // Create a layout
        let length = self.actual_args[1].1.clone();
        let alignment = self.actual_args[2].1.clone();
        let new_length = self.actual_args[3].1.clone();
        // We need to this to check for consistency between the realloc layout arg and the
        // initial alloc layout.
        let layout_param = AbstractValue::make_from(
            Expression::HeapBlockLayout {
                length,
                alignment: alignment.clone(),
                source: LayoutSource::ReAlloc,
            },
            1,
        );
        // We need this to keep track of the new length
        let new_length_layout = AbstractValue::make_from(
            Expression::HeapBlockLayout {
                length: new_length,
                alignment,
                source: LayoutSource::ReAlloc,
            },
            1,
        );

        // Get a layout path and update the environment
        let layout_path = Path::new_layout(heap_block_path)
            .refine_paths(&self.block_visitor.bv.current_environment);
        self.block_visitor
            .bv
            .current_environment
            .update_value_at(layout_path.clone(), new_length_layout);
        let layout_path2 = Path::new_layout(layout_path);
        self.block_visitor
            .bv
            .current_environment
            .update_value_at(layout_path2, layout_param);

        // Return the original heap block reference as the result
        self.actual_args[0].1.clone()
    }

    /// Set the call result to an offset derived from the arguments. Does no checking.
    #[logfn_inputs(TRACE)]
    fn handle_arith_offset(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_args.len() == 2);
        let base_val = &self.actual_args[0].1;
        let offset_val = &self.actual_args[1].1;
        base_val.offset(offset_val.clone())
    }

    /// Update the state to reflect a call to an intrinsic binary operation that returns a tuple
    /// of an operation result, modulo its max value, and a flag that indicates if the max value
    /// was exceeded.
    #[logfn_inputs(TRACE)]
    fn handle_checked_binary_operation(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_args.len() == 2);
        if let Some((target_place, _)) = &self.destination {
            let bin_op = match self.callee_known_name {
                KnownNames::StdIntrinsicsMulWithOverflow => mir::BinOp::Mul,
                _ => assume_unreachable!(),
            };
            let target_path = self.block_visitor.visit_place(target_place);
            let path0 = Path::new_field(target_path.clone(), 0)
                .refine_paths(&self.block_visitor.bv.current_environment);
            let path1 = Path::new_field(target_path.clone(), 1)
                .refine_paths(&self.block_visitor.bv.current_environment);
            let target_type = self
                .block_visitor
                .bv
                .type_visitor
                .get_target_path_type(&path0, self.block_visitor.bv.current_span);
            let left = self.actual_args[0].1.clone();
            let right = self.actual_args[1].1.clone();
            let modulo = target_type.modulo_value();
            let (modulo_result, overflow_flag) = if !modulo.is_bottom() {
                let (result, overflow_flag) = BlockVisitor::<E>::do_checked_binary_op(
                    bin_op,
                    target_type.clone(),
                    left,
                    right,
                );
                (result.remainder(target_type.modulo_value()), overflow_flag)
            } else {
                let (result, overflow_flag) = BlockVisitor::<E>::do_checked_binary_op(
                    bin_op,
                    target_type.clone(),
                    left,
                    right,
                );
                // todo: figure out an expression that represents the truncated overflow of a
                // signed operation.
                let unknown_typed_value = AbstractValue::make_from(
                    Expression::Variable {
                        path: path0.clone(),
                        var_type: target_type.clone(),
                    },
                    (path0.path_length() as u64) + 1,
                );
                (
                    overflow_flag.conditional_expression(unknown_typed_value, result),
                    overflow_flag,
                )
            };
            self.block_visitor
                .bv
                .current_environment
                .update_value_at(path0, modulo_result);
            self.block_visitor
                .bv
                .current_environment
                .update_value_at(path1, overflow_flag);
            AbstractValue::make_from(
                Expression::Variable {
                    path: target_path.clone(),
                    var_type: target_type,
                },
                (target_path.path_length() as u64) + 1,
            )
        } else {
            assume_unreachable!();
        }
    }

    /// Set the call result to an offset derived from the arguments.
    /// Checks that the resulting offset is either in bounds or one
    /// byte past the end of an allocated object.
    #[logfn_inputs(TRACE)]
    fn handle_offset(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_args.len() == 2);
        let base_val = &self.actual_args[0].1;
        let offset_val = &self.actual_args[1].1;
        let result = base_val.offset(offset_val.clone());
        if self.block_visitor.bv.check_for_errors && self.function_being_analyzed_is_root() {
            self.check_offset(&result)
        }
        result
    }

    /// Checks that the offset is either in bounds or one byte past the end of an allocated object.
    #[logfn_inputs(TRACE)]
    fn check_offset(&mut self, offset: &AbstractValue) {
        if let Expression::Offset { left, right, .. } = &offset.expression {
            let ge_zero = right.greater_or_equal(Rc::new(ConstantDomain::I128(0).into()));
            let mut len = left.clone();
            if let Expression::Reference(path) = &left.expression {
                if matches!(&path.value, PathEnum::HeapBlock{..}) {
                    let layout_path = Path::new_layout(path.clone());
                    if let Expression::HeapBlockLayout { length, .. } = &self
                        .block_visitor
                        .bv
                        .lookup_path_and_refine_result(
                            layout_path,
                            ExpressionType::NonPrimitive.as_rustc_type(self.block_visitor.bv.tcx),
                        )
                        .expression
                    {
                        len = length.clone();
                    }
                }
            };
            let le_one_past =
                right.less_or_equal(len.addition(Rc::new(ConstantDomain::I128(1).into())));
            let in_range = ge_zero.and(le_one_past);
            let (in_range_as_bool, entry_cond_as_bool) = self
                .block_visitor
                .check_condition_value_and_reachability(&in_range);
            //todo: eventually give a warning if in_range_as_bool is unknown. For now, that is too noisy.
            if entry_cond_as_bool.unwrap_or(true) && !in_range_as_bool.unwrap_or(true) {
                let span = self.block_visitor.bv.current_span;
                let message = "effective offset is outside allocated range";
                let warning = self
                    .block_visitor
                    .bv
                    .cv
                    .session
                    .struct_span_warn(span, message);
                self.block_visitor.bv.emit_diagnostic(warning);
            }
        }
    }

    /// Gets the size in bytes of the type parameter T of the std::mem::size_of<T> function.
    /// Returns and unknown value of type u128 if T is not a concrete type.
    #[logfn_inputs(TRACE)]
    fn handle_size_of(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_args.is_empty());
        let sym = rustc_span::Symbol::intern("T");
        let t = (self.callee_generic_argument_map.as_ref())
            .expect("std::mem::size_of must be called with generic arguments")
            .get(&sym)
            .expect("std::mem::size must have generic argument T");
        let param_env = self.block_visitor.bv.tcx.param_env(self.callee_def_id);
        if let Ok(ty_and_layout) = self.block_visitor.bv.tcx.layout_of(param_env.and(*t)) {
            Rc::new((ty_and_layout.layout.size.bytes() as u128).into())
        } else {
            AbstractValue::make_typed_unknown(ExpressionType::U128)
        }
    }

    #[logfn_inputs(TRACE)]
    fn get_function_constant_args(
        &self,
        actual_args: &[(Rc<Path>, Rc<AbstractValue>)],
    ) -> Vec<(Rc<Path>, Rc<AbstractValue>)> {
        let mut result = vec![];
        for (path, value) in self.block_visitor.bv.current_environment.value_map.iter() {
            if let Expression::CompileTimeConstant(ConstantDomain::Function(..)) = &value.expression
            {
                for (i, (arg_path, arg_val)) in actual_args.iter().enumerate() {
                    if (*path) == *arg_path || path.is_rooted_by(arg_path) {
                        let param_path_root = Path::new_parameter(i + 1);
                        let param_path = path.replace_root(arg_path, param_path_root);
                        result.push((param_path, value.clone()));
                        break;
                    } else {
                        match &arg_val.expression {
                            Expression::Reference(ipath)
                            | Expression::Variable { path: ipath, .. } => {
                                if (*path) == *ipath || path.is_rooted_by(ipath) {
                                    let param_path_root = Path::new_parameter(i + 1);
                                    let param_path = path.replace_root(arg_path, param_path_root);
                                    result.push((param_path, value.clone()));
                                    break;
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        for (i, (path, value)) in actual_args.iter().enumerate() {
            if let PathEnum::Alias { value: val } = &path.value {
                if *val == *value {
                    if let Expression::CompileTimeConstant(ConstantDomain::Function(..)) =
                        &value.expression
                    {
                        let param_path = Path::new_parameter(i + 1);
                        result.push((param_path, value.clone()));
                    }
                }
            }
        }
        result
    }

    /// Give diagnostic or mark the call chain as angelic, depending on self.bv.options.diag_level
    #[logfn_inputs(TRACE)]
    pub fn deal_with_missing_summary(&mut self) {
        self.report_missing_summary();
        let argument_type_hint = if let Some(func) = &self.callee_func_ref {
            format!(" (foreign fn argument key: {})", func.argument_type_key)
        } else {
            "".to_string()
        };
        info!(
            "function {} can't be reliably analyzed because it calls function {} which could not be summarized{}.",
            utils::summary_key_str(self.block_visitor.bv.tcx, self.block_visitor.bv.def_id),
            utils::summary_key_str(self.block_visitor.bv.tcx, self.callee_def_id),
            argument_type_hint,
        );
        debug!("def_id {:?}", self.callee_def_id);
    }

    /// Give diagnostic, depending on self.bv.options.diag_level
    #[logfn_inputs(TRACE)]
    fn report_missing_summary(&mut self) {
        match self.block_visitor.bv.cv.options.diag_level {
            DiagLevel::RELAXED => {
                // Assume the callee is perfect and assume the caller and all of its callers are perfect
                // little angels as well. This cuts down on false positives caused by missing post
                // conditions.
                self.block_visitor.bv.assume_function_is_angelic = true;
            }
            DiagLevel::STRICT => {
                // Assume the callee is perfect and that the caller does not need to prove any
                // preconditions and that the callee guarantees no post conditions.
            }
            DiagLevel::PARANOID => {
                if self.block_visitor.bv.check_for_errors {
                    // Give a diagnostic about this call, and make it the programmer's problem.
                    let error = self.block_visitor.bv.cv.session.struct_span_err(
                        self.block_visitor.bv.current_span,
                        "the called function could not be summarized, all bets are off",
                    );
                    self.block_visitor.bv.emit_diagnostic(error);
                }
            }
        }
    }

    /// If we are checking for errors and have not assumed the preconditions of the called function
    /// and we are not in angelic mode and have not already reported an error for this call,
    /// then check the preconditions and report any conditions that are not known to hold at this point.
    #[logfn_inputs(TRACE)]
    pub fn check_preconditions_if_necessary(&mut self, function_summary: &Summary) {
        if self.block_visitor.bv.check_for_errors
            && !self.block_visitor.bv.assume_preconditions_of_next_call
            && !self
                .block_visitor
                .bv
                .already_reported_errors_for_call_to
                .contains(&self.callee_fun_val)
        {
            self.check_function_preconditions(function_summary);
        } else {
            self.block_visitor.bv.assume_preconditions_of_next_call = false;
        }
    }

    /// Checks if the preconditions obtained from the summary of the function being called
    /// are met by the current state and arguments of the calling function.
    /// Preconditions that are definitely false and reachable cause diagnostic messages.
    /// Preconditions that are maybe false become preconditions of the calling function
    /// unless the calling function is an analysis root, in which case a diagnostic message is issued.
    #[logfn_inputs(TRACE)]
    fn check_function_preconditions(&mut self, function_summary: &Summary) {
        verify!(self.block_visitor.bv.check_for_errors);
        for precondition in &function_summary.preconditions {
            let mut refined_condition = precondition
                .condition
                .refine_parameters(
                    self.actual_args,
                    self.block_visitor.bv.fresh_variable_offset,
                )
                .refine_paths(&self.block_visitor.bv.current_environment);
            if self
                .block_visitor
                .bv
                .current_environment
                .entry_condition
                .as_bool_if_known()
                .is_none()
            {
                refined_condition = refined_condition.refine_with(
                    &self.block_visitor.bv.current_environment.entry_condition,
                    0,
                );
            }
            let (refined_precondition_as_bool, entry_cond_as_bool) = self
                .block_visitor
                .check_condition_value_and_reachability(&refined_condition);

            if refined_precondition_as_bool.unwrap_or(false) {
                // The precondition is definitely true.
                continue;
            };

            let warn;
            if !refined_precondition_as_bool.unwrap_or(true) {
                // The precondition is definitely false.
                if entry_cond_as_bool.unwrap_or(false) {
                    // We always get to this call
                    self.issue_diagnostic_for_call(precondition, false);
                    return;
                } else {
                    // Promote the precondition, but be assertive.
                    // When the caller fails to meet the precondition, failure is certain.
                    warn = false;
                }
            } else {
                warn = true;
            }

            // If the current function is not an analysis root, promote the precondition, subject to a k-limit.
            if !self.function_being_analyzed_is_root()
                && self.block_visitor.bv.preconditions.len() < k_limits::MAX_INFERRED_PRECONDITIONS
            {
                // Promote the callee precondition to a precondition of the current function.
                // Unless, of course, if the precondition is already a precondition of the
                // current function.
                let seen_precondition = self.block_visitor.bv.preconditions.iter().any(|pc| {
                    pc.spans.last() == precondition.spans.last()
                        || pc.provenance == precondition.provenance
                });
                if seen_precondition {
                    continue;
                }
                let promoted_condition = self
                    .block_visitor
                    .bv
                    .current_environment
                    .entry_condition
                    .logical_not()
                    .or(refined_condition);
                let mut stacked_spans = vec![self.block_visitor.bv.current_span];
                stacked_spans.append(&mut precondition.spans.clone());
                let promoted_precondition = Precondition {
                    condition: promoted_condition,
                    message: precondition.message.clone(),
                    provenance: precondition.provenance.clone(),
                    spans: stacked_spans,
                };
                self.block_visitor
                    .bv
                    .preconditions
                    .push(promoted_precondition);
                return;
            }

            // The precondition cannot be promoted, so the buck stops here.
            self.issue_diagnostic_for_call(precondition, warn);
        }
    }

    // Issue a diagnostic, but only if there isn't already a diagnostic for this
    // function call.
    #[logfn_inputs(TRACE)]
    fn issue_diagnostic_for_call(&mut self, precondition: &Precondition, warn: bool) {
        if self.block_visitor.bv.check_for_errors
            && !self
                .block_visitor
                .bv
                .already_reported_errors_for_call_to
                .contains(&self.callee_fun_val)
        {
            self.block_visitor
                .emit_diagnostic_for_precondition(precondition, warn);
            self.block_visitor
                .bv
                .already_reported_errors_for_call_to
                .insert(self.callee_fun_val.clone());
        }
    }

    /// Updates the current state to reflect the effects of a normal return from the function call.
    #[logfn_inputs(TRACE)]
    pub fn transfer_and_refine_normal_return_state(&mut self, function_summary: &Summary) {
        let destination = self.destination;
        if let Some((place, target)) = &destination {
            // Assign function result to place
            let target_path = self.block_visitor.visit_place(place);
            let return_value_path = Path::new_result();

            // Transfer side effects
            if function_summary.is_computed && !function_summary.is_angelic {
                // Effects on the heap
                for (path, value) in function_summary.side_effects.iter() {
                    if path.is_rooted_by_abstract_heap_block() {
                        let rvalue = value
                            .clone()
                            .refine_parameters(
                                self.actual_args,
                                self.block_visitor.bv.fresh_variable_offset,
                            )
                            .refine_paths(&self.block_visitor.bv.current_environment);
                        self.block_visitor
                            .bv
                            .current_environment
                            .update_value_at(path.clone(), rvalue);
                    }
                    check_for_early_return!(self.block_visitor.bv);
                }

                // Effects on the call result
                self.transfer_and_refine(
                    &function_summary.side_effects,
                    target_path.clone(),
                    &return_value_path,
                    self.actual_args,
                );

                // Effects on the call arguments
                for (i, (target_path, _)) in self.actual_args.iter().enumerate() {
                    let parameter_path = Path::new_parameter(i + 1);
                    self.transfer_and_refine(
                        &function_summary.side_effects,
                        target_path.clone(),
                        &parameter_path,
                        self.actual_args,
                    );
                    check_for_early_return!(self.block_visitor.bv);
                }
            } else {
                // We don't know anything other than the return value type.
                // We'll assume there were no side effects and no preconditions (but check this later if possible).
                let result_type = self
                    .block_visitor
                    .bv
                    .type_visitor
                    .get_place_type(place, self.block_visitor.bv.current_span);
                let result = AbstractValue::make_from(
                    Expression::UninterpretedCall {
                        callee: self.callee_fun_val.clone(),
                        arguments: self
                            .actual_args
                            .iter()
                            .map(|(_, arg)| arg.clone())
                            .collect(),
                        result_type,
                        path: return_value_path.clone(),
                    },
                    1,
                );
                self.block_visitor
                    .bv
                    .current_environment
                    .update_value_at(return_value_path, result);
            }

            // Add post conditions to entry condition
            let mut exit_condition = self
                .block_visitor
                .bv
                .current_environment
                .entry_condition
                .clone();
            if let Some(unwind_condition) = &function_summary.unwind_condition {
                exit_condition = exit_condition.and(unwind_condition.logical_not());
            }
            if let Some(post_condition) = &function_summary.post_condition {
                let mut return_value_env = Environment::default();
                let var_type = self
                    .block_visitor
                    .bv
                    .type_visitor
                    .get_place_type(place, self.block_visitor.bv.current_span);
                let result_val = AbstractValue::make_from(
                    Expression::Variable {
                        path: target_path,
                        var_type,
                    },
                    1,
                );
                let return_value_path =
                    Path::new_local(self.block_visitor.bv.fresh_variable_offset);

                return_value_env.update_value_at(return_value_path, result_val);
                let refined_post_condition = post_condition
                    .refine_parameters(
                        self.actual_args,
                        self.block_visitor.bv.fresh_variable_offset,
                    )
                    .refine_paths(&return_value_env);
                debug!(
                    "refined post condition before path refinement {:?}",
                    refined_post_condition
                );
                let refined_post_condition =
                    refined_post_condition.refine_paths(&self.block_visitor.bv.current_environment);
                debug!("refined post condition {:?}", refined_post_condition);
                exit_condition = exit_condition.and(refined_post_condition);
            }

            self.block_visitor.bv.current_environment.exit_conditions = self
                .block_visitor
                .bv
                .current_environment
                .exit_conditions
                .insert(*target, exit_condition);
        }
    }

    /// Handle the case where the called function does not complete normally.
    #[logfn_inputs(TRACE)]
    pub fn transfer_and_refine_cleanup_state(&mut self, function_summary: &Summary) {
        if let Some(cleanup_target) = self.cleanup {
            for (i, (target_path, _)) in self.actual_args.iter().enumerate() {
                let parameter_path = Path::new_parameter(i + 1);
                self.transfer_and_refine(
                    &function_summary.unwind_side_effects,
                    target_path.clone(),
                    &parameter_path,
                    self.actual_args,
                );
            }
            let mut exit_condition = self
                .block_visitor
                .bv
                .current_environment
                .entry_condition
                .clone();
            if let Some(unwind_condition) = &function_summary.unwind_condition {
                exit_condition = exit_condition.and(unwind_condition.clone());
            }
            self.block_visitor.bv.current_environment.exit_conditions = self
                .block_visitor
                .bv
                .current_environment
                .exit_conditions
                .insert(cleanup_target, exit_condition);
        }
    }

    /// Adds a (rpath, rvalue) pair to the current environment for every pair in effects
    /// for which the path is rooted by source_path and where rpath is path re-rooted with
    /// target_path and rvalue is value refined by replacing all occurrences of parameter values
    /// with the corresponding actual values.
    #[logfn_inputs(TRACE)]
    fn transfer_and_refine(
        &mut self,
        effects: &[(Rc<Path>, Rc<AbstractValue>)],
        target_path: Rc<Path>,
        source_path: &Rc<Path>,
        arguments: &[(Rc<Path>, Rc<AbstractValue>)],
    ) {
        for (path, value) in effects
            .iter()
            .filter(|(p, _)| (*p) == *source_path || p.is_rooted_by(source_path))
        {
            trace!("effect {:?} {:?}", path, value);
            let dummy_root = Path::new_local(999);
            let refined_dummy_root =
                Path::new_local(self.block_visitor.bv.fresh_variable_offset + 999);
            let tpath = path
                .replace_root(source_path, dummy_root)
                .refine_parameters(arguments, self.block_visitor.bv.fresh_variable_offset)
                .replace_root(&refined_dummy_root, target_path.clone())
                .refine_paths(&self.block_visitor.bv.current_environment);
            let rvalue = value
                .refine_parameters(arguments, self.block_visitor.bv.fresh_variable_offset)
                .refine_paths(&self.block_visitor.bv.current_environment);
            trace!("refined effect {:?} {:?}", tpath, rvalue);
            let rtype = rvalue.expression.infer_type();
            match &rvalue.expression {
                Expression::HeapBlock { .. } => {
                    if let PathEnum::QualifiedPath { selector, .. } = &tpath.value {
                        if let PathSelector::Slice(..) = selector.as_ref() {
                            let source_path = Path::get_as_path(rvalue.clone());
                            let target_type = type_visitor::get_element_type(
                                self.block_visitor.bv.type_visitor.get_path_rustc_type(
                                    &target_path,
                                    self.block_visitor.bv.current_span,
                                ),
                            );
                            self.block_visitor.copy_or_move_elements(
                                tpath.clone(),
                                source_path,
                                target_type,
                                false,
                            );
                            continue;
                        }
                    }
                    self.block_visitor
                        .bv
                        .current_environment
                        .update_value_at(tpath, rvalue);
                    continue;
                }
                Expression::HeapBlockLayout { source, .. } => {
                    match source {
                        LayoutSource::DeAlloc => {
                            self.purge_abstract_heap_address_from_environment(
                                &tpath,
                                &rvalue.expression,
                            );
                        }
                        LayoutSource::ReAlloc => {
                            let layout_argument_path = Path::new_layout(path.clone());
                            if let Some((_, val)) =
                                &effects.iter().find(|(p, _)| p.eq(&layout_argument_path))
                            {
                                let realloc_layout_val = val
                                    .clone()
                                    .refine_parameters(
                                        arguments,
                                        self.block_visitor.bv.fresh_variable_offset,
                                    )
                                    .refine_paths(&self.block_visitor.bv.current_environment);
                                self.update_zeroed_flag_for_heap_block_from_environment(
                                    &tpath,
                                    &realloc_layout_val.expression,
                                );
                            }
                        }
                        _ => {}
                    }

                    self.block_visitor
                        .bv
                        .current_environment
                        .update_value_at(tpath, rvalue);
                    continue;
                }
                Expression::Offset { .. } => {
                    if self.block_visitor.bv.check_for_errors
                        && self.function_being_analyzed_is_root()
                    {
                        self.check_offset(&rvalue);
                    }
                }
                Expression::Variable { path, .. } => {
                    let target_type = self
                        .block_visitor
                        .bv
                        .type_visitor
                        .get_path_rustc_type(&tpath, self.block_visitor.bv.current_span);
                    if let PathEnum::LocalVariable { ordinal } = &path.value {
                        if *ordinal >= self.block_visitor.bv.fresh_variable_offset {
                            // A fresh variable from the callee adds no information that is not
                            // already inherent in the target location.
                            self.block_visitor.bv.current_environment.value_map = self
                                .block_visitor
                                .bv
                                .current_environment
                                .value_map
                                .remove(&tpath);
                            continue;
                        }
                        if rtype == ExpressionType::NonPrimitive {
                            self.block_visitor.copy_or_move_elements(
                                tpath.clone(),
                                path.clone(),
                                target_type,
                                false,
                            );
                        }
                    } else if path.is_rooted_by_parameter() {
                        self.block_visitor
                            .bv
                            .current_environment
                            .update_value_at(tpath, rvalue);
                        continue;
                    } else if rtype == ExpressionType::NonPrimitive {
                        self.block_visitor.copy_or_move_elements(
                            tpath.clone(),
                            path.clone(),
                            target_type,
                            false,
                        );
                    }
                }
                _ => {}
            }
            if rtype != ExpressionType::NonPrimitive {
                self.block_visitor
                    .bv
                    .current_environment
                    .update_value_at(tpath, rvalue);
            }
            check_for_early_return!(self.block_visitor.bv);
        }
    }

    /// The heap block rooting layout_path has been deallocated in the function whose
    /// summary is being transferred to the current environment. If we know the identity of the
    /// heap block in the current environment, we need to check the validity of the deallocation
    /// and also have to delete any paths rooted in the heap block.
    #[logfn_inputs(TRACE)]
    fn purge_abstract_heap_address_from_environment(
        &mut self,
        layout_path: &Rc<Path>,
        new_layout_expression: &Expression,
    ) {
        if let PathEnum::QualifiedPath {
            qualifier,
            selector,
            ..
        } = &layout_path.value
        {
            if *selector.as_ref() == PathSelector::Layout {
                let old_layout = self.block_visitor.bv.lookup_path_and_refine_result(
                    layout_path.clone(),
                    ExpressionType::NonPrimitive.as_rustc_type(self.block_visitor.bv.tcx),
                );
                if let Expression::HeapBlockLayout { .. } = &old_layout.expression {
                    if self.block_visitor.bv.check_for_errors {
                        self.check_for_layout_consistency(
                            &old_layout.expression,
                            new_layout_expression,
                        );
                    }
                    let mut purged_map =
                        self.block_visitor.bv.current_environment.value_map.clone();
                    for (path, _) in self
                        .block_visitor
                        .bv
                        .current_environment
                        .value_map
                        .iter()
                        .filter(|(p, _)| p.is_rooted_by(&qualifier))
                    {
                        purged_map = purged_map.remove(path);
                    }
                    self.block_visitor.bv.current_environment.value_map = purged_map;
                }
            }
        } else {
            assume_unreachable!("Layout values should only be associated with layout paths");
        }
    }

    /// Following a reallocation we are no longer guaranteed that the resulting heap
    /// memory block has been zeroed out by the allocator. Search the environment for equivalent
    /// heap block values and update them to clear the zeroed flag (if set).
    #[logfn_inputs(DEBUG)]
    fn update_zeroed_flag_for_heap_block_from_environment(
        &mut self,
        layout_path: &Rc<Path>,
        new_layout_expression: &Expression,
    ) {
        if let PathEnum::QualifiedPath { qualifier, .. } = &layout_path.value {
            if self.block_visitor.bv.check_for_errors {
                let old_layout = self.block_visitor.bv.lookup_path_and_refine_result(
                    layout_path.clone(),
                    ExpressionType::NonPrimitive.as_rustc_type(self.block_visitor.bv.tcx),
                );
                self.check_for_layout_consistency(&old_layout.expression, new_layout_expression);
            }
            if let PathEnum::HeapBlock { value } = &qualifier.value {
                if let Expression::HeapBlock {
                    abstract_address,
                    is_zeroed,
                } = &value.expression
                {
                    if *is_zeroed {
                        let mut updated_value_map =
                            self.block_visitor.bv.current_environment.value_map.clone();
                        for (path, value) in
                            self.block_visitor.bv.current_environment.value_map.iter()
                        {
                            if let Expression::Reference(p) = &value.expression {
                                if let PathEnum::HeapBlock { value } = &p.value {
                                    if let Expression::HeapBlock {
                                        abstract_address: a,
                                        is_zeroed: z,
                                    } = &value.expression
                                    {
                                        if *abstract_address == *a && *z {
                                            let new_block = AbstractValue::make_from(
                                                Expression::HeapBlock {
                                                    abstract_address: *a,
                                                    is_zeroed: false,
                                                },
                                                1,
                                            );
                                            let new_block_path = Path::get_as_path(new_block);
                                            let new_reference =
                                                AbstractValue::make_reference(new_block_path);
                                            updated_value_map = updated_value_map
                                                .insert(path.clone(), new_reference);
                                        }
                                    }
                                }
                            }
                        }
                        self.block_visitor.bv.current_environment.value_map = updated_value_map;
                    }
                }
            }
        }
    }

    /// Checks that the layout used to allocate a pointer has an equivalent runtime value to the
    /// layout used to deallocate the pointer.
    /// Also checks that a pointer is deallocated at most once.
    #[logfn_inputs(TRACE)]
    fn check_for_layout_consistency(&mut self, old_layout: &Expression, new_layout: &Expression) {
        precondition!(self.block_visitor.bv.check_for_errors);
        if let (
            Expression::HeapBlockLayout {
                length: old_length,
                alignment: old_alignment,
                source: old_source,
            },
            Expression::HeapBlockLayout {
                length: new_length,
                alignment: new_alignment,
                source: new_source,
            },
        ) = (old_layout, new_layout)
        {
            if *old_source == LayoutSource::DeAlloc {
                let error = self.block_visitor.bv.cv.session.struct_span_err(
                    self.block_visitor.bv.current_span,
                    "the pointer points to memory that has already been deallocated",
                );
                self.block_visitor.bv.emit_diagnostic(error);
            }
            let layouts_match = old_length
                .equals(new_length.clone())
                .and(old_alignment.equals(new_alignment.clone()));
            let (layouts_match_as_bool, entry_cond_as_bool) = self
                .block_visitor
                .check_condition_value_and_reachability(&layouts_match);
            if entry_cond_as_bool.unwrap_or(true) && !layouts_match_as_bool.unwrap_or(false) {
                // The condition may be reachable and it may be false
                let message = format!(
                    "{}{} the pointer with layout information inconsistent with the allocation",
                    if entry_cond_as_bool.is_none() || layouts_match_as_bool.is_none() {
                        "possibly "
                    } else {
                        ""
                    },
                    if *new_source == LayoutSource::ReAlloc {
                        "reallocates"
                    } else {
                        "deallocates"
                    }
                );
                let error = self
                    .block_visitor
                    .bv
                    .cv
                    .session
                    .struct_span_err(self.block_visitor.bv.current_span, &message);
                self.block_visitor.bv.emit_diagnostic(error);
            }
        }
    }

    /// Extracts the string from an AbstractDomain that is required to be a string literal.
    /// This is the case for helper MIRAI helper functions that are hidden in the documentation
    /// and that are required to be invoked via macros that ensure that the argument providing
    /// this value is always a string literal.
    #[logfn_inputs(TRACE)]
    fn coerce_to_string(&mut self, value: &AbstractValue) -> Rc<String> {
        match &value.expression {
            Expression::CompileTimeConstant(ConstantDomain::Str(s)) => s.clone(),
            _ => {
                if self.block_visitor.bv.check_for_errors {
                    let error = self.block_visitor.bv.cv.session.struct_span_err(
                        self.block_visitor.bv.current_span,
                        "this argument should be a string literal, do not call this function directly",
                    );
                    self.block_visitor.bv.emit_diagnostic(error);
                }
                Rc::new("dummy argument".to_string())
            }
        }
    }

    /// Returns true if the function being analyzed is an analysis root.
    #[logfn_inputs(TRACE)]
    pub fn function_being_analyzed_is_root(&mut self) -> bool {
        self.block_visitor.bv.active_calls.len() <= 1
    }
}
