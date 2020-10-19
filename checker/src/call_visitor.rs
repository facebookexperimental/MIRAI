// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use log_derive::*;
use mirai_annotations::*;
use rustc_ast::ast;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty::subst::{GenericArg, GenericArgKind, SubstsRef};
use rustc_middle::ty::{AdtDef, Ty, TyCtxt, TyKind};
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
use crate::path::{Path, PathEnum, PathRefinement, PathSelector};
use crate::smt_solver::SmtResult;
use crate::summaries::{Precondition, Summary};
use crate::tag_domain::Tag;
use crate::{abstract_value, type_visitor, utils};

pub struct CallVisitor<'call, 'block, 'analysis, 'compilation, 'tcx, E> {
    pub block_visitor: &'call mut BlockVisitor<'block, 'analysis, 'compilation, 'tcx, E>,
    pub callee_def_id: DefId,
    pub callee_func_ref: Option<Rc<FunctionReference>>,
    pub callee_fun_val: Rc<AbstractValue>,
    pub callee_generic_arguments: Option<SubstsRef<'tcx>>,
    pub callee_known_name: KnownNames,
    pub callee_generic_argument_map: Option<HashMap<rustc_span::Symbol, GenericArg<'tcx>>>,
    pub actual_args: &'call [(Rc<Path>, Rc<AbstractValue>)],
    pub actual_argument_types: &'call [Ty<'tcx>],
    pub cleanup: Option<mir::BasicBlock>,
    pub destination: Option<(mir::Place<'tcx>, mir::BasicBlock)>,
    pub environment_before_call: Environment,
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
        callee_generic_argument_map: Option<HashMap<rustc_span::Symbol, GenericArg<'tcx>>>,
        environment_before_call: Environment,
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
                environment_before_call,
                function_constant_args: &[],
            }
        } else {
            unreachable!("caller should supply a constant function")
        }
    }

    /// Summarize the referenced function, specialized by its generic arguments and the actual
    /// values of any function parameters. Then cache it.
    #[logfn_inputs(TRACE)]
    pub fn create_and_cache_function_summary(
        &mut self,
        func_args: Option<Vec<Rc<FunctionReference>>>,
    ) -> Summary {
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
                self.block_visitor.bv.active_calls_map,
            );
            body_visitor.type_visitor.actual_argument_types = self.actual_argument_types.into();
            body_visitor.type_visitor.generic_arguments = self.callee_generic_arguments;
            body_visitor.type_visitor.generic_argument_map =
                self.callee_generic_argument_map.clone();
            body_visitor.analyzing_static_var = self.block_visitor.bv.analyzing_static_var;
            let elapsed_time = self.block_visitor.bv.start_instant.elapsed();
            let mut summary =
                body_visitor.visit_body(self.function_constant_args, self.actual_argument_types);
            let call_was_angelic = body_visitor.assume_function_is_angelic;
            trace!("summary {:?} {:?}", self.callee_def_id, summary);
            let signature = self.get_function_constant_signature(self.function_constant_args);
            if let Some(func_ref) = &self.callee_func_ref {
                // If there is already a computed summary in the cache, we are in a recursive loop
                // and hence have to join the summaries.
                let previous_summary = self
                    .block_visitor
                    .bv
                    .cv
                    .summary_cache
                    .get_summary_for_call_site(&func_ref, func_args);
                if previous_summary.is_computed {
                    summary.join_side_effects(previous_summary)
                }

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
        }
        Summary::default()
    }

    /// If self.callee_def_id is a trait (virtual) then this tries to get the def_id of the
    /// concrete method that implements the given virtual method and returns the summary of that,
    /// computing it if necessary.
    #[logfn_inputs(TRACE)]
    fn try_to_devirtualize(&mut self) {
        if self
            .block_visitor
            .bv
            .tcx
            .is_mir_available(self.callee_def_id)
        {
            return;
        }
        if let Some(gen_args) = self.callee_generic_arguments {
            if !utils::are_concrete(gen_args) {
                trace!("non concrete generic args {:?}", gen_args);
                return;
            }
            // The parameter environment of the caller provides a resolution context for the callee.
            let param_env = rustc_middle::ty::ParamEnv::reveal_all();
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
                self.callee_def_id = resolved_def_id;
                let resolved_ty = self.block_visitor.bv.tcx.type_of(resolved_def_id);
                let resolved_map = self
                    .block_visitor
                    .bv
                    .type_visitor
                    .get_generic_arguments_map(resolved_def_id, instance.substs, &[]);
                let specialized_resolved_ty = self
                    .block_visitor
                    .bv
                    .type_visitor
                    .specialize_generic_argument_type(resolved_ty, &resolved_map);
                trace!(
                    "devirtualize resolved def_id {:?}: {:?}",
                    resolved_def_id,
                    specialized_resolved_ty
                );
                let func_const = self
                    .block_visitor
                    .visit_function_reference(
                        resolved_def_id,
                        specialized_resolved_ty,
                        instance.substs,
                    )
                    .clone();
                self.callee_func_ref = if let ConstantDomain::Function(fr) = &func_const {
                    self.callee_known_name = fr.known_name;
                    Some(fr.clone())
                } else {
                    None
                };
                self.callee_fun_val = Rc::new(func_const.into());
                self.callee_generic_arguments = Some(instance.substs);
                self.callee_generic_argument_map = self
                    .block_visitor
                    .bv
                    .type_visitor
                    .get_generic_arguments_map(
                        resolved_def_id,
                        instance.substs,
                        self.actual_argument_types,
                    );
            }
        }
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
            .filter_map(|(_, v)| self.block_visitor.get_func_ref(v))
            .collect();
        if vec.is_empty() {
            return None;
        }
        Some(vec)
    }

    /// Returns a summary of the function to call, obtained from the summary cache.
    #[logfn_inputs(TRACE)]
    pub fn get_function_summary(&mut self) -> Option<Summary> {
        self.try_to_devirtualize();
        if let Some(func_ref) = &self.callee_func_ref.clone() {
            // If the actual arguments include any function constants, collect them together
            // and pass them to get_summary_for_function_constant so that their signatures
            // can be included in the type specific key that is used to look up non generic
            // predefined summaries.

            //get_function_constant_signature???
            let func_args: Option<Vec<Rc<FunctionReference>>> =
                if !self.function_constant_args.is_empty() {
                    Some(
                        self.function_constant_args
                            .iter()
                            .filter_map(|(_, v)| self.block_visitor.get_func_ref(v))
                            .collect(),
                    )
                } else {
                    // common case
                    None
                };
            let call_depth = *self
                .block_visitor
                .bv
                .active_calls_map
                .get(&func_ref.def_id.unwrap())
                .unwrap_or(&0u64);
            let result = self
                .block_visitor
                .bv
                .cv
                .summary_cache
                .get_summary_for_call_site(&func_ref, func_args.clone())
                .clone();
            if result.is_computed || func_ref.def_id.is_none() {
                return Some(result);
            }
            if call_depth < 3 {
                let mut summary = self.create_and_cache_function_summary(func_args);
                if call_depth >= 1 {
                    summary.post_condition = None;

                    // Widen summary at call level 1 so that the level 0 call sees the widened values.
                    if call_depth == 1 {
                        summary.widen_side_effects();
                    }
                    let signature =
                        self.get_function_constant_signature(self.function_constant_args);
                    self.block_visitor
                        .bv
                        .cv
                        .summary_cache
                        .set_summary_for_call_site(&func_ref, signature, summary.clone());
                }
                return Some(summary);
            } else {
                // Probably a statically unbounded self recursive call. Use an empty summary and let
                // earlier calls do the joining and widening required.
                let mut summary = Summary::default();
                summary
                    .side_effects
                    .push((Path::new_result(), Rc::new(abstract_value::BOTTOM)));
                summary.is_computed = true;
                let signature = self.get_function_constant_signature(self.function_constant_args);
                self.block_visitor
                    .bv
                    .cv
                    .summary_cache
                    .set_summary_for_call_site(&func_ref, signature, summary.clone());
                return Some(summary);
            }
        }
        None
    }

    /// If this call is to an implementation of the std::clone::Clone::clone trait method
    /// then make sure any model fields and tag fields are copied to the result as well.
    /// If there is no MIR implementation available for the clone method, then fall back to a
    /// deep copy (after calling deal_with_missing_summary).
    #[logfn_inputs(DEBUG)]
    pub fn handle_clone(&mut self, summary: &Summary) {
        if let Some((place, _)) = &self.destination {
            checked_assume!(self.actual_args.len() == 1);
            let source_path = Path::new_deref(self.actual_args[0].0.clone())
                .refine_paths(&self.block_visitor.bv.current_environment, 0);
            let target_type = self
                .block_visitor
                .bv
                .type_visitor
                .get_rustc_place_type(place, self.block_visitor.bv.current_span);
            let target_path = self.block_visitor.visit_place(place);
            if !summary.is_computed {
                self.deal_with_missing_summary();
                // Now just do a deep copy and carry on.
                self.block_visitor.bv.copy_or_move_elements(
                    target_path,
                    source_path,
                    target_type,
                    false,
                );
            } else {
                self.transfer_and_refine_into_current_environment(summary);
                // Since the clone code is arbitrary it might not have copied model fields and tag fields.
                // So just copy them again.
                let value_map = self.block_visitor.bv.current_environment.value_map.clone();
                for (path, value) in value_map.iter().filter(|(p, _)| {
                    if let PathEnum::QualifiedPath { selector, .. } = &p.value {
                        matches!(
                            **selector,
                            PathSelector::ModelField(..) | PathSelector::TagField
                        ) && p.is_rooted_by(&source_path)
                    } else {
                        false
                    }
                }) {
                    let target_path = path.replace_root(&source_path, target_path.clone());
                    self.block_visitor
                        .bv
                        .current_environment
                        .update_value_at(target_path, value.clone());
                }
            }
            self.use_entry_condition_as_exit_condition();
        } else {
            assume_unreachable!();
        }
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
            KnownNames::MiraiAddTag => {
                checked_assume!(self.actual_args.len() == 1);
                self.handle_add_tag();
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
            KnownNames::MiraiDoesNotHaveTag => {
                checked_assume!(self.actual_args.len() == 1);
                self.handle_check_tag(false);
                return true;
            }
            KnownNames::MiraiGetModelField => {
                self.handle_get_model_field();
                return true;
            }
            KnownNames::MiraiHasTag => {
                checked_assume!(self.actual_args.len() == 1);
                self.handle_check_tag(true);
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
            KnownNames::MiraiResult => {
                if let Some((place, _)) = &self.destination {
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
                } else {
                    assume_unreachable!();
                }
                self.use_entry_condition_as_exit_condition();
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
                self.use_entry_condition_as_exit_condition();
                return true;
            }
            KnownNames::StdFutureFromGenerator => {
                checked_assume!(self.actual_args.len() == 1);
                let generator_fun_val = self.actual_args[0].1.clone();
                let generator_fun_ref = self
                    .block_visitor
                    .get_func_ref(&generator_fun_val)
                    .expect("a fun ref");
                let generator_def_id = generator_fun_ref.def_id.expect("a def id");
                let environment_before_call = self.block_visitor.bv.current_environment.clone();
                let mut block_visitor = BlockVisitor::<E>::new(self.block_visitor.bv);
                let mut generator_call_visitor = CallVisitor::new(
                    &mut block_visitor,
                    generator_def_id,
                    None,
                    None,
                    environment_before_call,
                    ConstantDomain::Function(generator_fun_ref),
                );
                self.block_visitor.bv.async_fn_summary =
                    generator_call_visitor.get_function_summary();
                return true;
            }
            KnownNames::StdIntrinsicsCopy | KnownNames::StdIntrinsicsCopyNonOverlapping => {
                self.handle_copy_non_overlapping();
                return true;
            }
            KnownNames::StdIntrinsicsDiscriminantValue => {
                self.handle_discriminant_value();
                return true;
            }
            KnownNames::StdIntrinsicsTransmute => {
                self.handle_transmute();
                return true;
            }
            KnownNames::StdIntrinsicsWriteBytes => {
                self.handle_write_bytes();
                return true;
            }
            KnownNames::StdMemReplace => {
                self.handle_mem_replace();
                return true;
            }
            KnownNames::StdPtrSwapNonOverlapping => {
                self.handle_swap_non_overlapping();
                return true;
            }
            KnownNames::StdPanickingBeginPanic | KnownNames::StdPanickingBeginPanicFmt => {
                if self.block_visitor.bv.check_for_errors {
                    self.report_calls_to_special_functions();
                }
                if let Some((_, target)) = &self.destination {
                    self.block_visitor
                        .bv
                        .current_environment
                        .exit_conditions
                        .insert_mut(*target, abstract_value::FALSE.into());
                }
                return true;
            }
            _ => {
                let result = self.try_to_inline_special_function();
                if !result.is_bottom() {
                    if let Some((place, _)) = &self.destination {
                        let target_path = self.block_visitor.visit_place(place);
                        self.block_visitor
                            .bv
                            .current_environment
                            .update_value_at(target_path, result);
                        self.use_entry_condition_as_exit_condition();
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Use this for terminators that deterministically transfer control to a single successor block.
    /// Such blocks, obviously, do not alter their entry path condition.
    #[logfn_inputs(TRACE)]
    fn use_entry_condition_as_exit_condition(&mut self) {
        if let Some((_, target)) = &self.destination {
            let exit_condition = self
                .block_visitor
                .bv
                .current_environment
                .entry_condition
                .clone();
            self.block_visitor
                .bv
                .current_environment
                .exit_conditions
                .insert_mut(*target, exit_condition);
        }
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
                    .bv
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

                // If the condition is always true, this assumption is redundant. If false, the
                // assumption is ignored. Otherwise, no diagnostics are emitted.
                let message = if cond_as_bool == Some(true) {
                    "assumption is provably true and can be deleted"
                } else if cond_as_bool == Some(false) {
                    "assumption is provably false and it will be ignored in the assertion"
                } else {
                    return;
                };
                let span = self.block_visitor.bv.current_span;
                let warning = self
                    .block_visitor
                    .bv
                    .cv
                    .session
                    .struct_span_warn(span, message);
                self.block_visitor.bv.emit_diagnostic(warning);
            }
            KnownNames::MiraiPostcondition => {
                assume!(self.actual_args.len() == 3); // The type checker ensures this.
                let (_, assumption) = &self.actual_args[1];
                let (_, cond) = &self.actual_args[0];
                if !assumption.as_bool_if_known().unwrap_or(false) {
                    let message = self.coerce_to_string(&self.actual_args[2].0);
                    if self
                        .block_visitor
                        .check_condition(cond, message.as_ref(), true)
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
                let message = self.coerce_to_string(&self.actual_args[1].0);
                if let Some(warning) =
                    self.block_visitor
                        .check_condition(cond, message.as_ref(), false)
                {
                    // Push a precondition so that any known or unknown caller of this function
                    // is warned that this function will fail if the precondition is not met.
                    if !cond.expression.contains_local_variable()
                        && self.block_visitor.bv.preconditions.len()
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
                            message: warning,
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

                let msg = if matches!(self.callee_known_name, KnownNames::StdPanickingBeginPanic) {
                    self.coerce_to_string(&self.actual_args[0].0)
                } else {
                    let arguments_struct_path = self.actual_args[0]
                        .0
                        .refine_paths(&self.block_visitor.bv.current_environment, 0);
                    let pieces_path_fat = Path::new_field(arguments_struct_path, 0)
                        .refine_paths(&self.block_visitor.bv.current_environment, 0);
                    let pieces_path_thin = Path::new_field(pieces_path_fat, 0)
                        .refine_paths(&self.block_visitor.bv.current_environment, 0);
                    let index = Rc::new(0u128.into());
                    let piece0_path_fat = Path::new_index(pieces_path_thin, index)
                        .refine_paths(&self.block_visitor.bv.current_environment, 0);
                    self.coerce_to_string(&piece0_path_fat)
                };
                if msg.contains("entered unreachable code")
                    || msg.contains("not yet implemented")
                    || msg.starts_with("unrecoverable: ")
                {
                    // We treat unreachable!() as an assumption rather than an assertion to prove.
                    // unimplemented!() is unlikely to be a programmer mistake, so need to fixate on that either.
                    // unrecoverable! is way for the programmer to indicate that termination is not a mistake.
                    return;
                } else if path_cond.is_none() && msg.as_ref() == "statement is reachable" {
                    // verify_unreachable should always complain if possibly reachable
                    // and the current function is public or root.
                    path_cond = Some(true);
                };

                let span = self.block_visitor.bv.current_span;

                if path_cond.unwrap_or(false)
                    && self.block_visitor.bv.function_being_analyzed_is_root()
                {
                    // We always get to this call and we have to assume that the function will
                    // get called, so keep the message certain.
                    // Don't, however, complain about panics in the standard contract summaries
                    if std::env::var("MIRAI_START_FRESH").is_err() {
                        let err = self
                            .block_visitor
                            .bv
                            .cv
                            .session
                            .struct_span_warn(span, msg.as_ref());
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
                    if !condition.expression.contains_local_variable() {
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
                let arg_type: ExpressionType = self.actual_argument_types[0].kind().into();
                let bit_length = arg_type.bit_length();
                self.actual_args[0]
                    .1
                    .intrinsic_bit_vector_unary(bit_length, self.callee_known_name)
            }
            KnownNames::StdIntrinsicsCtlzNonzero | KnownNames::StdIntrinsicsCttzNonzero => {
                checked_assume!(self.actual_args.len() == 1);
                if self.block_visitor.bv.check_for_errors {
                    let non_zero = self.actual_args[0].1.not_equals(Rc::new(0u128.into()));
                    self.block_visitor
                        .check_condition(&non_zero, "argument is zero", false);
                }
                let arg_type: ExpressionType = self.actual_argument_types[0].kind().into();
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
            KnownNames::StdIntrinsicsMinAlignOfVal => self.handle_min_align_of_val(),
            KnownNames::StdIntrinsicsMulWithOverflow => self.handle_checked_binary_operation(),
            KnownNames::StdIntrinsicsOffset => self.handle_offset(),
            KnownNames::StdIntrinsicsSizeOf => self.handle_size_of(),
            KnownNames::StdIntrinsicsSizeOfVal => self.handle_size_of_val(),
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
        trace!("self.actual_args {:?}", self.actual_args);
        trace!(
            "self.actual_argument_types {:?}",
            self.actual_argument_types
        );
        trace!(
            "self.function_constant_args {:?}",
            self.function_constant_args
        );
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
        if let TyKind::Tuple(tuple_types) = generic_argument_types[1].kind() {
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
                    .refine_paths(&self.block_visitor.bv.current_environment, 0);
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
        let closure_ref_ty;
        if let TyKind::Ref(_, ty, _) = closure_ty.kind() {
            closure_ref_ty = closure_ty;
            closure_ty = ty;
        } else {
            let tcx = self.block_visitor.bv.tcx;
            closure_ref_ty = tcx.mk_mut_ref(tcx.lifetimes.re_static, closure_ty);
        }
        let mut argument_map = self.callee_generic_argument_map.clone();
        if type_visitor::get_def_id_from_closure(closure_ty).is_some() {
            actual_args.insert(0, self.actual_args[0].clone());
            actual_argument_types.insert(0, closure_ref_ty);
            //todo: could this be a generator?
            if let TyKind::Closure(def_id, substs) = closure_ty.kind() {
                argument_map = self
                    .block_visitor
                    .bv
                    .type_visitor
                    .get_generic_arguments_map(*def_id, substs.as_closure().substs, &[]);
            }
        }

        let function_constant_args = self.block_visitor.get_function_constant_args(&actual_args);
        let callee_func_ref = self.block_visitor.get_func_ref(&callee);

        let function_summary = if let Some(func_ref) = &callee_func_ref {
            let func_const = ConstantDomain::Function(func_ref.clone());
            let def_id = func_ref.def_id.expect("defined when used here");
            let generic_arguments = self.block_visitor.bv.cv.substs_cache.get(&def_id).cloned();
            if let Some(substs) = generic_arguments {
                argument_map = self
                    .block_visitor
                    .bv
                    .type_visitor
                    .get_generic_arguments_map(def_id, substs, &actual_argument_types)
            }
            let environment_before_call = self.block_visitor.bv.current_environment.clone();
            let mut block_visitor = BlockVisitor::<E>::new(self.block_visitor.bv);
            let mut indirect_call_visitor = CallVisitor::new(
                &mut block_visitor,
                def_id,
                generic_arguments,
                argument_map,
                environment_before_call,
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
                if summary.is_computed || summary.is_angelic {
                    indirect_call_visitor.transfer_and_refine_into_current_environment(&summary);
                    return;
                }
            }
            if self.block_visitor.bv.check_for_errors {
                let saved_callee_def_id = self.callee_def_id;
                self.callee_def_id = def_id;
                self.deal_with_missing_summary();
                self.callee_def_id = saved_callee_def_id;
            }
            Summary::default()
        } else {
            if self.block_visitor.bv.check_for_errors {
                warn!("unknown callee {:?}", callee);
                self.deal_with_missing_summary();
            }
            Summary::default()
        };

        self.transfer_and_refine_into_current_environment(&function_summary);
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
            let abstract_value = AbstractValue::make_typed_unknown(expression_type, path.clone());
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
            self.block_visitor
                .bv
                .current_environment
                .exit_conditions
                .insert_mut(*target, exit_condition);
        } else {
            assume_unreachable!();
        }
    }

    /// Attach a tag to the first and only value in actual_args.
    /// The tag type is indicated by a generic argument.
    #[logfn_inputs(TRACE)]
    fn handle_add_tag(&mut self) {
        precondition!(self.actual_args.len() == 1);

        if let Some(tag) = self.extract_tag_kind_and_propagation_set() {
            let source_pointer_path = self.actual_args[0].0.clone();
            let source_pointer_rustc_type = self.actual_argument_types[0];
            let source_thin_pointer_path = Path::get_path_to_thin_pointer_at_offset_0(
                self.block_visitor.bv.tcx,
                &self.block_visitor.bv.current_environment,
                &source_pointer_path,
                source_pointer_rustc_type,
            )
            .unwrap_or(source_pointer_path);
            let source_path = Path::new_deref(source_thin_pointer_path)
                .refine_paths(&self.block_visitor.bv.current_environment, 0);
            trace!("MiraiAddTag: tagging {:?} with {:?}", tag, source_path);

            // Check if the tagged value has a pointer type (e.g., a reference).
            // Emit an error message if so.
            let source_rustc_type = self
                .block_visitor
                .bv
                .type_visitor
                .get_path_rustc_type(&source_path, self.block_visitor.bv.current_span);
            if self.block_visitor.bv.check_for_errors && source_rustc_type.is_any_ptr() {
                let err = self.block_visitor.bv.cv.session.struct_span_err(
                    self.block_visitor.bv.current_span,
                    "the macro add_tag! expects its argument to be a reference to a non-reference value",
                );
                self.block_visitor.bv.emit_diagnostic(err);
            }

            // Augment the tags associated at the source with a new tag.
            self.block_visitor
                .bv
                .attach_tag_to_elements(tag, source_path, source_rustc_type);
        }

        // Update exit conditions.
        self.use_entry_condition_as_exit_condition();
    }

    /// Adds the first and only value in actual_args to the path condition of the destination.
    /// No check is performed, since we get to assume this condition without proof.
    #[logfn_inputs(TRACE)]
    fn handle_assume(&mut self) {
        precondition!(self.actual_args.len() == 1);
        let assumed_condition = &self.actual_args[0].1;
        // Ignore assertion of the assumed condition, when it is provably false
        // or add the condition to assertion.
        let exit_condition = if let Some(false) = assumed_condition.as_bool_if_known() {
            self.block_visitor
                .bv
                .current_environment
                .entry_condition
                .and(Rc::new(abstract_value::TRUE))
        } else {
            self.block_visitor
                .bv
                .current_environment
                .entry_condition
                .and(assumed_condition.clone())
        };
        if let Some((_, target)) = &self.destination {
            self.block_visitor
                .bv
                .current_environment
                .exit_conditions
                .insert_mut(*target, exit_condition);
        } else {
            assume_unreachable!();
        }
        if let Some(cleanup_target) = self.cleanup {
            self.block_visitor
                .bv
                .current_environment
                .exit_conditions
                .insert_mut(cleanup_target, abstract_value::FALSE.into());
        }
    }

    /// Check if a tag has been attached to the first and only value in actual_args.
    /// The tag type is indicated by a generic argument.
    #[logfn_inputs(TRACE)]
    fn handle_check_tag(&mut self, checking_presence: bool) {
        precondition!(self.actual_args.len() == 1);

        let result: Option<Rc<AbstractValue>>;
        if let Some(tag) = self.extract_tag_kind_and_propagation_set() {
            let source_pointer_path = self.actual_args[0].0.clone();
            let source_pointer_rustc_type = self.actual_argument_types[0];
            let source_thin_pointer_path = Path::get_path_to_thin_pointer_at_offset_0(
                self.block_visitor.bv.tcx,
                &self.block_visitor.bv.current_environment,
                &source_pointer_path,
                source_pointer_rustc_type,
            )
            .unwrap_or(source_pointer_path);
            let source_path = Path::new_deref(source_thin_pointer_path)
                .refine_paths(&self.block_visitor.bv.current_environment, 0);
            trace!(
                "MiraiCheckTag: checking if {:?} has {}been tagged with {:?}",
                source_path,
                (if checking_presence { "" } else { "never " }),
                tag,
            );

            // Check if the tagged value has a pointer type (e.g., a reference).
            // Emit an error message if so.
            let source_rustc_type = self
                .block_visitor
                .bv
                .type_visitor
                .get_path_rustc_type(&source_path, self.block_visitor.bv.current_span);
            if self.block_visitor.bv.check_for_errors && source_rustc_type.is_any_ptr() {
                let err = self.block_visitor.bv.cv.session.struct_span_err(
                    self.block_visitor.bv.current_span,
                    format!(
                        "the macro {} expects its first argument to be a reference to a non-reference value",
                        if checking_presence { "has_tag! "} else { "does_not_have_tag!" },
                    ).as_str(),
                );
                self.block_visitor.bv.emit_diagnostic(err);
            }

            // If the value located at source_path has sub-components, extract its tag field.
            // Otherwise, the source value is a scalar, i.e., tags are associated with it directly,
            // so we use the value itself as the tag field value.
            let tag_field_value = if !source_rustc_type.is_scalar() {
                self.block_visitor
                    .bv
                    .extract_tag_field_of_non_scalar_value_at(&source_path, source_rustc_type)
                    .1
            } else {
                self.block_visitor
                    .bv
                    .lookup_path_and_refine_result(source_path.clone(), source_rustc_type)
            };

            // Decide the result of has_tag! or does_not_have_tag!.
            let mut check_result =
                AbstractValue::make_tag_check(tag_field_value, tag, checking_presence);

            // If the tag can be propagated through sub-components, and source_path is rooted by a function parameter,
            // we need to check the tag on the values that can contain source_path as a sub-component. Note that if
            // source_path is rooted by a local variable, MIRAI has already propagated the tag to source_path when the
            // tag was added to the value that contains source_path as a sub-component.
            // Operationally, source_path is a qualified path and we check if any of its prefix has the tag (when checking_presence = true),
            // or if all of its prefixes does not have the tag (when checking_presence = false).
            if tag.is_propagated_by(TagPropagation::SubComponent)
                && source_path.is_rooted_by_parameter()
            {
                let mut path_prefix = &source_path;
                while let PathEnum::QualifiedPath { qualifier, .. } = &path_prefix.value {
                    path_prefix = qualifier;

                    let path_prefix_rustc_type = self
                        .block_visitor
                        .bv
                        .type_visitor
                        .get_path_rustc_type(&path_prefix, self.block_visitor.bv.current_span);
                    if !path_prefix_rustc_type.is_scalar() {
                        let tag_field_value = self
                            .block_visitor
                            .bv
                            .extract_tag_field_of_non_scalar_value_at(
                                &path_prefix,
                                path_prefix_rustc_type,
                            )
                            .1;

                        if checking_presence {
                            // We are checking presence of a tag. It is equivalent to *any* prefix having the tag.
                            // Thus we use a logical or.
                            check_result = check_result.or(AbstractValue::make_tag_check(
                                tag_field_value,
                                tag,
                                checking_presence,
                            ));

                            // Exits the loop if check_result is already true.
                            if check_result.as_bool_if_known().unwrap_or(false) {
                                break;
                            }
                        } else {
                            // We are checking absence of a tag. It is equivalent to *all* prefixes not having the tag.
                            // Thus we use a logical and.
                            check_result = check_result.and(AbstractValue::make_tag_check(
                                tag_field_value,
                                tag,
                                checking_presence,
                            ));

                            // Exits the loop if check_result is already false.
                            if !check_result.as_bool_if_known().unwrap_or(true) {
                                break;
                            }
                        }
                    }
                }
            }

            result = Some(check_result);
        } else {
            result = None;
        }

        // Return the abstract result and update exit conditions.
        let destination = &self.destination;
        if let Some((place, _)) = destination {
            let target_path = self.block_visitor.visit_place(place);
            self.block_visitor.bv.current_environment.update_value_at(
                target_path.clone(),
                result.unwrap_or_else(|| {
                    AbstractValue::make_typed_unknown(ExpressionType::Bool, target_path)
                }),
            );
        } else {
            assume_unreachable!("expected the function call has a destination");
        }
        self.use_entry_condition_as_exit_condition();
    }

    /// Update the state so that the call result is the value of the model field (or the default
    /// value if there is no field).
    #[logfn_inputs(TRACE)]
    fn handle_get_model_field(&mut self) {
        let destination = self.destination;
        if let Some((place, _)) = &destination {
            let target_type = self
                .block_visitor
                .bv
                .type_visitor
                .get_rustc_place_type(place, self.block_visitor.bv.current_span);
            checked_assume!(self.actual_args.len() == 3);

            // The current value, if any, of the model field are a set of (path, value) pairs
            // where each path is rooted by qualifier.model_field(..)
            let mut qualifier = self.actual_args[0].0.clone();
            if matches!(&self.actual_argument_types[0].kind(), TyKind::Ref{..}) {
                qualifier = Path::new_deref(qualifier);
            }
            let field_name = self.coerce_to_string(&self.actual_args[1].0);
            let source_path = Path::new_model_field(qualifier, field_name)
                .refine_paths(&self.block_visitor.bv.current_environment, 0);

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
                self.block_visitor.bv.copy_or_move_elements(
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
                    Expression::Reference(path)
                    | Expression::InitialParameterValue { path, .. }
                    | Expression::Variable { path, .. }
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
                        self.block_visitor.bv.copy_or_move_elements(
                            target_path,
                            source_path,
                            target_type,
                            true,
                        );
                    }
                }
            }
            self.use_entry_condition_as_exit_condition();
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
            self.block_visitor
                .bv
                .current_environment
                .exit_conditions
                .insert_mut(*target, exit_condition);
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
            self.block_visitor
                .bv
                .current_environment
                .exit_conditions
                .insert_mut(*target, exit_condition);
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
            //todo: give diagnostic if the condition contains a local variable.
            let message = self.coerce_to_string(&self.actual_args[1].0);
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
            let mut qualifier = self.actual_args[0].0.clone();
            if matches!(&self.actual_argument_types[0].kind(), TyKind::Ref{..}) {
                qualifier = Path::new_deref(qualifier);
            }
            let field_name = self.coerce_to_string(&self.actual_args[1].0);
            let target_path = Path::new_model_field(qualifier, field_name)
                .refine_paths(&self.block_visitor.bv.current_environment, 0);
            let source_path = self.actual_args[2].0.clone();
            let target_type = self.actual_argument_types[2];
            self.block_visitor.bv.copy_or_move_elements(
                target_path,
                source_path,
                target_type,
                true,
            );
            let exit_condition = self
                .block_visitor
                .bv
                .current_environment
                .entry_condition
                .clone();
            self.block_visitor
                .bv
                .current_environment
                .exit_conditions
                .insert_mut(*target, exit_condition);
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
            .refine_paths(&self.block_visitor.bv.current_environment, 0);
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
        let source_path = self.actual_args[0].0.clone();
        let target_root = self.actual_args[1].0.clone();
        let count = self.actual_args[2].1.clone();
        let target_path = Path::new_slice(target_root, count)
            .refine_paths(&self.block_visitor.bv.current_environment, 0);
        let collection_type = self.actual_argument_types[0];
        self.block_visitor.bv.copy_or_move_elements(
            target_path,
            source_path,
            collection_type,
            false,
        );
        self.use_entry_condition_as_exit_condition();
    }

    /// Returns the value of the discriminant for the variant in 'v',
    /// cast to a `u64`; if `T` has no discriminant, returns 0.
    #[logfn_inputs(TRACE)]
    fn handle_discriminant_value(&mut self) {
        checked_assume!(self.actual_args.len() == 1);
        if let Some((place, _)) = &self.destination {
            let discriminant_path =
                Path::new_discriminant(Path::new_deref(self.actual_args[0].0.clone()))
                    .refine_paths(&self.block_visitor.bv.current_environment, 0);
            let mut discriminant_value = self.block_visitor.bv.lookup_path_and_refine_result(
                discriminant_path,
                self.block_visitor.bv.tcx.types.u128,
            );
            // If `T` has no discriminant, return 0.
            match self.callee_generic_arguments {
                None => assume_unreachable!(
                    "expected discriminant_value function call to have a generic argument"
                ),
                Some(rustc_gen_args) => {
                    checked_assume!(rustc_gen_args.len() == 1);
                    match rustc_gen_args[0].unpack() {
                        GenericArgKind::Type(ty) => match ty.kind() {
                            TyKind::Adt(..) if ty.is_enum() => {}
                            TyKind::Generator(..) => {}
                            _ => {
                                discriminant_value = Rc::new(ConstantDomain::U128(0).into());
                            }
                        },
                        _ => {
                            // The rust type checker should ensure that the generic argument is a type.
                            assume_unreachable!(
                            "expected the generic argument of discriminant_value function calls to be a type"
                        );
                        }
                    }
                }
            }
            let target_path = self.block_visitor.visit_place(place);
            self.block_visitor
                .bv
                .current_environment
                .update_value_at(target_path, discriminant_value);
        }
        self.use_entry_condition_as_exit_condition();
    }

    /// Swaps a slice of elements from the source to the destination.
    #[logfn_inputs(TRACE)]
    fn handle_swap_non_overlapping(&mut self) {
        checked_assume!(self.actual_args.len() == 3);
        let ty = self.actual_argument_types[0];
        let target_root = self.actual_args[0].0.clone();
        let source_root = self.actual_args[1].0.clone();
        let count = self.actual_args[2].1.clone();
        let source_slice = Path::new_slice(source_root.clone(), count.clone())
            .refine_paths(&self.block_visitor.bv.current_environment, 0);
        let target_slice = Path::new_slice(target_root.clone(), count.clone())
            .refine_paths(&self.block_visitor.bv.current_environment, 0);
        let temp_root = Path::new_local(999_999);
        let temp_slice = Path::new_slice(temp_root.clone(), count);
        self.block_visitor
            .bv
            .copy_or_move_elements(temp_slice, target_root, ty, true);
        self.block_visitor
            .bv
            .copy_or_move_elements(target_slice, source_root, ty, true);
        self.block_visitor
            .bv
            .copy_or_move_elements(source_slice, temp_root, ty, true);
        self.use_entry_condition_as_exit_condition();
    }

    /// Returns a new heap memory block with the given byte length.
    #[logfn_inputs(TRACE)]
    fn handle_rust_alloc(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_args.len() == 2);
        let length = self.actual_args[0].1.clone();
        let alignment = self.actual_args[1].1.clone();
        let tcx = self.block_visitor.bv.tcx;
        let byte_slice = tcx.mk_slice(tcx.types.u8);
        let heap_path = Path::get_as_path(
            self.block_visitor
                .bv
                .get_new_heap_block(length, alignment, false, byte_slice),
        );
        AbstractValue::make_reference(heap_path)
    }

    /// Returns a new heap memory block with the given byte length and with the zeroed flag set.
    #[logfn_inputs(TRACE)]
    fn handle_rust_alloc_zeroed(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_args.len() == 2);
        let length = self.actual_args[0].1.clone();
        let alignment = self.actual_args[1].1.clone();
        let tcx = self.block_visitor.bv.tcx;
        let byte_slice = tcx.mk_slice(tcx.types.u8);
        let heap_path = Path::get_as_path(
            self.block_visitor
                .bv
                .get_new_heap_block(length, alignment, true, byte_slice),
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
            .refine_paths(&self.block_visitor.bv.current_environment, 0);
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
                .refine_paths(&self.block_visitor.bv.current_environment, 0);
            let path1 = Path::new_field(target_path.clone(), 1)
                .refine_paths(&self.block_visitor.bv.current_environment, 0);
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
                let unknown_typed_value =
                    AbstractValue::make_typed_unknown(target_type.clone(), path0.clone());
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
            AbstractValue::make_typed_unknown(target_type, target_path)
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
        if self.block_visitor.bv.check_for_errors
            && self.block_visitor.bv.function_being_analyzed_is_root()
        {
            self.block_visitor.bv.check_offset(&result)
        }
        result
    }

    /// Moves `source` into the referenced `dest`, returning the previous `dest` value.
    #[logfn_inputs(TRACE)]
    fn handle_mem_replace(&mut self) {
        checked_assume!(self.actual_args.len() == 2);
        let dest_path = Path::new_deref(self.actual_args[0].0.clone())
            .refine_paths(&self.block_visitor.bv.current_environment, 0);
        let source_path = &self.actual_args[1].0;
        if let Some((place, _)) = &self.destination {
            let target_path = self.block_visitor.visit_place(place);
            let root_rustc_type = self
                .block_visitor
                .bv
                .type_visitor
                .get_rustc_place_type(place, self.block_visitor.bv.current_span);
            // Return the old value of dest_path
            self.block_visitor.bv.copy_or_move_elements(
                target_path,
                dest_path.clone(),
                root_rustc_type,
                true,
            );
            // Move value at source path into dest path
            self.block_visitor.bv.copy_or_move_elements(
                dest_path,
                source_path.clone(),
                root_rustc_type,
                true,
            );
        }
        self.use_entry_condition_as_exit_condition();
    }

    /// Gets the size in bytes of the type parameter T of the std::mem::size_of<T> function.
    /// Returns an unknown value of type u128 if T is not a concrete type.
    #[logfn_inputs(TRACE)]
    fn handle_size_of(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_args.is_empty());
        let sym = rustc_span::Symbol::intern("T");
        let t = (self.callee_generic_argument_map.as_ref())
            .expect("std::intrinsics::size_of must be called with generic arguments")
            .get(&sym)
            .expect("std::intrinsics::size_of must have generic argument T")
            .expect_ty();
        let param_env = self.block_visitor.bv.tcx.param_env(self.callee_def_id);
        if let Ok(ty_and_layout) = self.block_visitor.bv.tcx.layout_of(param_env.and(t)) {
            if !ty_and_layout.is_unsized() {
                return Rc::new((ty_and_layout.layout.size.bytes() as u128).into());
            }
        }
        let path = self.block_visitor.visit_place(
            &self
                .destination
                .expect("std::intrinsics::size_of should have a destination")
                .0,
        );
        AbstractValue::make_typed_unknown(ExpressionType::U128, path)
    }

    /// Returns the [ABI]-required minimum alignment of the type of the value that `val` points to.
    ///
    /// Every reference to a value of the type `T` must be a multiple of this number.
    fn handle_min_align_of_val(&mut self) -> Rc<AbstractValue> {
        let param_env = self.block_visitor.bv.tcx.param_env(self.callee_def_id);
        checked_assume!(self.actual_argument_types.len() == 1);
        let t = self.actual_argument_types[0];
        if let Ok(ty_and_layout) = self.block_visitor.bv.tcx.layout_of(param_env.and(t)) {
            return Rc::new((ty_and_layout.layout.align.abi.bytes() as u128).into());
        }
        // todo: need an expression that resolves to the value size once the value is known (typically after call site refinement).
        let path = self.block_visitor.visit_place(
            &self
                .destination
                .expect("std::intrinsics::min_align_of_val should have a destination")
                .0,
        );
        AbstractValue::make_typed_unknown(ExpressionType::U128, path)
    }

    /// Returns the size of the pointed-to value in bytes.
    ///
    /// This is usually the same as `size_of::<T>()`. However, when `T` *has* no
    /// statically-known size, e.g., a slice [`[T]`][slice] or a [trait object],
    /// then `size_of_val` can be used to get the dynamically-known size.
    #[logfn_inputs(TRACE)]
    fn handle_size_of_val(&mut self) -> Rc<AbstractValue> {
        let param_env = self.block_visitor.bv.tcx.param_env(self.callee_def_id);
        checked_assume!(self.actual_argument_types.len() == 1);
        let t = self.actual_argument_types[0];
        checked_assume!(self.actual_args.len() == 1);
        let val = &self.actual_args[0].1;
        if matches!(val.expression, Expression::HeapBlock {..}) {
            // If the value is heap allocated, we can get its size from the layout path
            let heap_path = Path::get_as_path(val.clone());
            let layout_path = Path::new_layout(heap_path);
            let layout_val = self.block_visitor.bv.lookup_path_and_refine_result(
                layout_path,
                ExpressionType::NonPrimitive.as_rustc_type(self.block_visitor.bv.tcx),
            );
            if let Expression::HeapBlockLayout { length, .. } = &layout_val.expression {
                return length.clone();
            }
        } else if type_visitor::is_slice_pointer(t.kind()) {
            let elem_t = type_visitor::get_element_type(t);
            if let Ok(ty_and_layout) = self.block_visitor.bv.tcx.layout_of(param_env.and(elem_t)) {
                if !ty_and_layout.is_unsized() {
                    let elem_size_val: Rc<AbstractValue> =
                        Rc::new((ty_and_layout.layout.size.bytes() as u128).into());
                    let length_path = Path::new_length(self.actual_args[0].0.clone())
                        .refine_paths(&self.block_visitor.bv.current_environment, 0);
                    let len_val = self.block_visitor.bv.lookup_path_and_refine_result(
                        length_path,
                        ExpressionType::Usize.as_rustc_type(self.block_visitor.bv.tcx),
                    );
                    return len_val.multiply(elem_size_val);
                }
            }
        }
        let sym = rustc_span::Symbol::intern("T");
        let t = (self.callee_generic_argument_map.as_ref())
            .expect("std::intrinsics::size_of_val must be called with generic arguments")
            .get(&sym)
            .expect("std::intrinsics::size_of_val must have generic argument T")
            .expect_ty();
        if let Ok(ty_and_layout) = self.block_visitor.bv.tcx.layout_of(param_env.and(t)) {
            if !ty_and_layout.is_unsized() {
                return Rc::new((ty_and_layout.layout.size.bytes() as u128).into());
            }
        }
        // todo: need an expression that resolves to the value size once the value is known (typically after call site refinement).
        let path = self.block_visitor.visit_place(
            &self
                .destination
                .expect("std::intrinsics::size_of_value should have a destination")
                .0,
        );
        AbstractValue::make_typed_unknown(ExpressionType::U128, path)
    }

    /// Reinterprets the bits of a value of one type as another type.
    ///
    /// Both types must have the same size. Neither the original, nor the result,
    /// may be an [invalid value](../../nomicon/what-unsafe-does.html).
    ///
    /// `transmute` is semantically equivalent to a bitwise move of one type
    /// into another. It copies the bits from the source value into the
    /// destination value, then forgets the original. It's equivalent to C's
    /// `memcpy` under the hood, just like `transmute_copy`.
    #[logfn_inputs(TRACE)]
    fn handle_transmute(&mut self) {
        checked_assume!(self.actual_args.len() == 1);
        let mut source_path = self.actual_args[0].0.clone();
        let source_rustc_type = self
            .callee_generic_arguments
            .expect("rustc type error")
            .get(0)
            .expect("rustc type error")
            .expect_ty();
        if let Some((place, _)) = &self.destination {
            let mut target_path = self.block_visitor.visit_place(place);
            let target_rustc_type = self
                .block_visitor
                .bv
                .type_visitor
                .get_rustc_place_type(place, self.block_visitor.bv.current_span);
            // todo: use copy_field_bits for these cases (and others)
            if type_visitor::is_thin_pointer(&target_rustc_type.kind()) {
                source_path = Path::get_path_to_thin_pointer_at_offset_0(
                    self.block_visitor.bv.tcx,
                    &self.block_visitor.bv.current_environment,
                    &source_path,
                    source_rustc_type,
                )
                .unwrap_or(source_path);
            } else if type_visitor::is_thin_pointer(&source_rustc_type.kind()) {
                target_path = Path::get_path_to_thin_pointer_at_offset_0(
                    self.block_visitor.bv.tcx,
                    &self.block_visitor.bv.current_environment,
                    &target_path,
                    target_rustc_type,
                )
                .unwrap_or(target_path);
            }

            fn add_leaf_fields_for<'a>(
                path: Rc<Path>,
                def: &'a AdtDef,
                substs: SubstsRef<'a>,
                tcx: TyCtxt<'a>,
                accumulator: &mut Vec<(Rc<Path>, Ty<'a>)>,
            ) {
                let variant = def.variants.iter().next().expect("at least one variant");
                for (i, field) in variant.fields.iter().enumerate() {
                    let field_path = Path::new_field(path.clone(), i);
                    let field_ty = field.ty(tcx, substs);
                    if let TyKind::Adt(def, substs) = field_ty.kind() {
                        add_leaf_fields_for(field_path, def, substs, tcx, accumulator)
                    } else {
                        accumulator.push((field_path, field_ty))
                    }
                }
            };

            match (source_rustc_type.kind(), target_rustc_type.kind()) {
                (
                    TyKind::Adt(source_def, source_substs),
                    TyKind::Adt(target_def, target_substs),
                ) => {
                    let mut source_fields = Vec::new();
                    add_leaf_fields_for(
                        source_path,
                        source_def,
                        source_substs,
                        self.block_visitor.bv.tcx,
                        &mut source_fields,
                    );
                    let mut target_fields = Vec::new();
                    add_leaf_fields_for(
                        target_path,
                        target_def,
                        target_substs,
                        self.block_visitor.bv.tcx,
                        &mut target_fields,
                    );
                    self.copy_field_bits(source_fields, target_fields);
                }
                _ => {
                    self.block_visitor.bv.copy_or_move_elements(
                        target_path,
                        source_path,
                        target_rustc_type,
                        true,
                    );
                }
            }
        }
        self.use_entry_condition_as_exit_condition();
    }

    /// Assign abstract values to the target fields that are consistent with the concrete values
    /// that will arise at runtime if the sequential (packed) bytes of the source fields are copied to the
    /// target fields on a little endian machine.
    #[logfn_inputs(INFO)]
    fn copy_field_bits(
        &mut self,
        source_fields: Vec<(Rc<Path>, Ty<'tcx>)>,
        target_fields: Vec<(Rc<Path>, Ty<'tcx>)>,
    ) {
        let source_len = source_fields.len();
        let mut source_field_index = 0;
        let mut copied_source_bits = 0;
        for (target_path, target_type) in target_fields.into_iter() {
            if source_field_index >= source_len {
                // The rust compiler should not permit this to happen
                assume_unreachable!("transmute called on types with different bit lengths");
            }
            let (source_path, source_type) = &source_fields[source_field_index];
            let source_path =
                source_path.refine_paths(&self.block_visitor.bv.current_environment, 0);
            let mut val = self
                .block_visitor
                .bv
                .lookup_path_and_refine_result(source_path.clone(), source_type);
            if copied_source_bits > 0 {
                // discard the lower order bits from val since they have already been copied to a previous target field
                val = val.unsigned_shift_right(copied_source_bits);
            }
            let source_bits = ExpressionType::from(source_type.kind()).bit_length();
            let target_expression_type = ExpressionType::from(target_type.kind());
            let mut target_bits_to_write = target_expression_type.bit_length();
            if source_bits - copied_source_bits >= target_bits_to_write {
                // target field can be completely assigned from bits of source field value
                if source_bits - copied_source_bits > target_bits_to_write {
                    // discard higher order bits since they wont fit into the target field
                    val = val.unsigned_modulo(target_bits_to_write);
                }
                self.block_visitor
                    .bv
                    .current_environment
                    .update_value_at(target_path, val.transmute(target_expression_type));
                copied_source_bits += target_bits_to_write;
                if copied_source_bits == source_bits {
                    source_field_index += 1;
                    copied_source_bits = 0;
                }
            } else {
                // target field needs bits from multiple source fields
                let mut written_target_bits = source_bits - copied_source_bits;
                target_bits_to_write -= written_target_bits;
                val = val.unsigned_modulo(written_target_bits);
                loop {
                    // Get another field
                    source_field_index += 1;
                    if source_field_index >= source_len {
                        // The rust compiler should not permit this to happen
                        assume_unreachable!("transmute called on types with different bit lengths");
                    }
                    let (source_path, source_type) = &source_fields[source_field_index];
                    let source_path =
                        source_path.refine_paths(&self.block_visitor.bv.current_environment, 0);
                    let source_bits = ExpressionType::from(source_type.kind()).bit_length();
                    let mut next_val = self
                        .block_visitor
                        .bv
                        .lookup_path_and_refine_result(source_path.clone(), source_type);
                    // discard higher order bits that wont fit into the target field
                    next_val = next_val.unsigned_modulo(target_bits_to_write);
                    // shift next value to the left, making space for val in the lower order bits
                    next_val = next_val.unsigned_shift_left(written_target_bits);
                    // update val to include next_val (in its higher order bits, thanks to the shift left above)
                    val = next_val.addition(val);
                    if source_bits >= target_bits_to_write {
                        // We are done with this target field
                        self.block_visitor.bv.current_environment.update_value_at(
                            target_path.clone(),
                            val.transmute(target_expression_type.clone()),
                        );
                        if source_bits == target_bits_to_write {
                            copied_source_bits = 0;
                            source_field_index += 1;
                        } else {
                            copied_source_bits = target_bits_to_write;
                        }
                        break;
                    }
                    target_bits_to_write -= source_bits;
                    written_target_bits += source_bits;
                }
            }
        }
    }

    #[logfn_inputs(TRACE)]
    fn handle_write_bytes(&mut self) {
        checked_assume!(self.actual_args.len() == 3);
        let dest_path = Path::new_deref(self.actual_args[0].0.clone())
            .refine_paths(&self.block_visitor.bv.current_environment, 0);
        let dest_type = self.actual_argument_types[0];
        let source_path = self.actual_args[1].0.clone();
        let byte_value = &self.actual_args[1].1;
        let count_value = self.actual_args[2].1.clone();
        let elem_type = self
            .callee_generic_arguments
            .expect("write_bytes<T>")
            .get(0)
            .expect("write_bytes<T>")
            .expect_ty();
        let mut elem_size = self.block_visitor.bv.type_visitor.get_type_size(elem_type);
        fn repeated_bytes(mut elem_size: u64, byte_value: &Rc<AbstractValue>) -> Rc<AbstractValue> {
            let const_8: Rc<AbstractValue> = Rc::new(8u128.into());
            let mut source_value = byte_value.clone();
            while elem_size > 1 {
                source_value = source_value
                    .shift_left(const_8.clone())
                    .bit_or(byte_value.clone());
                elem_size -= 1;
            }
            source_value
        }
        if elem_type.is_primitive() {
            let dest_pattern = Path::new_slice(dest_path, count_value);
            let source_value = repeated_bytes(elem_size, byte_value);
            self.block_visitor
                .bv
                .current_environment
                .update_value_at(dest_pattern, source_value);
        } else if let Expression::CompileTimeConstant(count) = &count_value.expression {
            if let ConstantDomain::U128(count) = count {
                if let TyKind::Adt(..) | TyKind::Tuple(..) = &elem_type.kind() {
                    for i in 0..(*count as usize) {
                        let dest_field = Path::new_field(dest_path.clone(), i);
                        let field_type = self
                            .block_visitor
                            .bv
                            .type_visitor
                            .get_path_rustc_type(&dest_field, self.block_visitor.bv.current_span);
                        let field_size =
                            self.block_visitor.bv.type_visitor.get_type_size(field_type);
                        elem_size -= field_size;
                        let field_value = repeated_bytes(field_size, byte_value);
                        self.block_visitor
                            .bv
                            .current_environment
                            .update_value_at(dest_field, field_value);
                        if elem_size == 0 {
                            break;
                        }
                    }
                } else {
                    if *count > 1 {
                        warn!(
                            "unhandled call to write_bytes<{:?}>({:?}: {:?}, {:?}, {:?})",
                            elem_type,
                            self.actual_args[0],
                            dest_type,
                            self.actual_args[1],
                            self.actual_args[2]
                        );
                    }
                    self.block_visitor.bv.copy_or_move_elements(
                        dest_path,
                        source_path,
                        elem_type,
                        false,
                    );
                }
            } else {
                assume_unreachable!("Rust type system should preclude this");
            }
        } else {
            warn!(
                "unhandled call to write_bytes at {:?}",
                self.block_visitor.bv.current_span
            );
            info!("elem_type {:?}", elem_type);
            info!("dest {:?}", self.actual_args[0]);
            info!("dest_type {:?}", dest_type);
            info!("val {:?}", self.actual_args[1]);
            info!("count {:?}", self.actual_args[2]);
        }
        self.use_entry_condition_as_exit_condition();
    }

    /// Give diagnostic or mark the call chain as angelic, depending on self.bv.options.diag_level
    #[logfn_inputs(TRACE)]
    pub fn deal_with_missing_summary(&mut self) {
        if self.block_visitor.might_be_reachable() {
            self.block_visitor.report_missing_summary();
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
    }

    /// Refines the summary using the call arguments and local environment and transfers
    /// the side effects of the summary into the current environment, while also checking
    /// preconditions and add the post conditions to the exit condition guarding the post call target block.
    #[logfn_inputs(TRACE)]
    pub fn transfer_and_refine_into_current_environment(&mut self, function_summary: &Summary) {
        trace!("def_id {:?}", self.callee_def_id);
        trace!("summary {:?}", function_summary);
        trace!("pre env {:?}", self.block_visitor.bv.current_environment);
        trace!(
            "target {:?} arguments {:?}",
            self.destination,
            self.actual_args
        );
        if function_summary.is_angelic
            && !self.block_visitor.bv.assume_function_is_angelic
            && self.block_visitor.might_be_reachable()
        {
            self.block_visitor.bv.assume_function_is_angelic = true;
        }
        self.check_preconditions_if_necessary(&function_summary);
        self.transfer_and_refine_normal_return_state(&function_summary);
        self.transfer_and_refine_cleanup_state(&function_summary);
        self.add_post_condition_to_exit_conditions(&function_summary);
        trace!("post env {:?}", self.block_visitor.bv.current_environment);
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
                    &None,
                    &self.environment_before_call,
                    self.block_visitor.bv.fresh_variable_offset,
                )
                .refine_paths(&self.block_visitor.bv.current_environment, 0);
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
                .bv
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
            if !self.block_visitor.bv.function_being_analyzed_is_root()
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
                if !promoted_condition.expression.contains_local_variable() {
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
                }
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
    /// The paths and expressions of the side-effects are refined in the context of the pre-state
    /// (the environment before the call executed), while the refined effects are applied to the
    /// current state.
    #[logfn_inputs(TRACE)]
    pub fn transfer_and_refine_normal_return_state(&mut self, function_summary: &Summary) {
        let destination = self.destination;
        if let Some((place, _)) = &destination {
            // Assign function result to place
            let target_path = self.block_visitor.visit_place(place);
            let result_path = &Some(target_path.clone());
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
                                result_path,
                                &self.environment_before_call,
                                self.block_visitor.bv.fresh_variable_offset,
                            )
                            .refine_paths(&self.block_visitor.bv.current_environment, 0);
                        self.block_visitor.bv.current_environment.update_value_at(
                            path.refine_parameters(
                                self.actual_args,
                                result_path,
                                &self.environment_before_call,
                                self.block_visitor.bv.fresh_variable_offset,
                            ),
                            rvalue,
                        );
                    }
                    check_for_early_return!(self.block_visitor.bv);
                }

                // Effects on the call result
                self.block_visitor.bv.transfer_and_refine(
                    &function_summary.side_effects,
                    target_path,
                    &return_value_path,
                    result_path,
                    self.actual_args,
                    &self.environment_before_call,
                );

                // Effects on the call arguments
                for (i, (target_path, _)) in self.actual_args.iter().enumerate() {
                    let parameter_path = Path::new_parameter(i + 1);
                    self.block_visitor.bv.transfer_and_refine(
                        &function_summary.side_effects,
                        target_path.clone(),
                        &parameter_path,
                        result_path,
                        self.actual_args,
                        &self.environment_before_call,
                    );
                    check_for_early_return!(self.block_visitor.bv);
                }
            } else {
                // We don't know anything other than the return value type.
                // We'll assume there were no side effects and no preconditions.
                let args = self.actual_args.iter().map(|(_, a)| a.clone()).collect();
                let result_type = self
                    .block_visitor
                    .bv
                    .type_visitor
                    .get_place_type(place, self.block_visitor.bv.current_span);
                let result =
                    self.callee_fun_val
                        .uninterpreted_call(args, result_type, return_value_path);
                self.block_visitor
                    .bv
                    .current_environment
                    .update_value_at(target_path, result);
            }
        }
    }

    /// If the function summary has a post condition, refine this and add it to the
    /// exit conditions for the current block.
    /// Note that this function has to be executed in the pre-state of the call.
    /// Any variables left in the post condition of the summary refers to its parameters
    /// and thus to the state of the current function as it was before making the
    /// call to function that is summarized by function_summary.
    #[logfn_inputs(TRACE)]
    pub fn add_post_condition_to_exit_conditions(&mut self, function_summary: &Summary) {
        let destination = self.destination;
        if let Some((place, target)) = &destination {
            let target_path = self.block_visitor.visit_place(place);
            let result_path = &Some(target_path);
            let mut exit_condition = self
                .block_visitor
                .bv
                .current_environment
                .entry_condition
                .clone();
            if let Some(unwind_condition) = &function_summary.unwind_condition {
                if exit_condition.as_bool_if_known().unwrap_or(true) {
                    let unwind_condition = unwind_condition
                        .refine_parameters(
                            self.actual_args,
                            &result_path,
                            &self.environment_before_call,
                            self.block_visitor.bv.fresh_variable_offset,
                        )
                        .refine_paths(&self.block_visitor.bv.current_environment, 0);
                    exit_condition = exit_condition.and(unwind_condition.logical_not());
                }
            }
            if exit_condition.as_bool_if_known().unwrap_or(true) {
                if let Some(post_condition) = &function_summary.post_condition {
                    let refined_post_condition = post_condition.refine_parameters(
                        self.actual_args,
                        &result_path,
                        &self.environment_before_call,
                        self.block_visitor.bv.fresh_variable_offset,
                    );
                    trace!(
                        "refined post condition before path refinement {:?}",
                        refined_post_condition
                    );
                    let refined_post_condition = refined_post_condition
                        .refine_paths(&self.block_visitor.bv.current_environment, 0);
                    trace!("refined post condition {:?}", refined_post_condition);
                    exit_condition = exit_condition.and(refined_post_condition);
                    trace!("post exit conditions {:?}", exit_condition);
                }
            }

            self.block_visitor
                .bv
                .current_environment
                .exit_conditions
                .insert_mut(*target, exit_condition);
        }
    }

    /// Handle the case where the called function does not complete normally.
    /// The paths and expressions of the side-effects are refined in the context of the pre-state
    /// (the environment before the call executed), while the refined effects are applied to the
    /// current state.
    #[logfn_inputs(TRACE)]
    pub fn transfer_and_refine_cleanup_state(&mut self, function_summary: &Summary) {
        if let Some(cleanup_target) = self.cleanup {
            for (i, (target_path, _)) in self.actual_args.iter().enumerate() {
                let parameter_path = Path::new_parameter(i + 1);
                self.block_visitor.bv.transfer_and_refine(
                    &function_summary.unwind_side_effects,
                    target_path.clone(),
                    &parameter_path,
                    &None,
                    self.actual_args,
                    &self.environment_before_call,
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
            self.block_visitor
                .bv
                .current_environment
                .exit_conditions
                .insert_mut(cleanup_target, exit_condition);
        }
    }

    /// Extracts the string from an AbstractDomain that is required to be a reference to a string literal.
    /// This is the case for helper MIRAI helper functions that are hidden in the documentation
    /// and that are required to be invoked via macros that ensure that the argument providing
    /// this value is always a string literal.
    #[logfn_inputs(TRACE)]
    fn coerce_to_string(&mut self, path: &Rc<Path>) -> Rc<str> {
        if let PathEnum::Alias { value } = &path.value {
            if let Expression::Reference(path) = &value.expression {
                if let PathEnum::Alias { value } = &path.value {
                    if let Expression::CompileTimeConstant(ConstantDomain::Str(s)) =
                        &value.expression
                    {
                        return s.clone();
                    }
                }
            }
        } else if let Some(value) = self.block_visitor.bv.current_environment.value_at(path) {
            if let Expression::Reference(path) = &value.expression {
                if let PathEnum::Alias { value } = &path.value {
                    if let Expression::CompileTimeConstant(ConstantDomain::Str(s)) =
                        &value.expression
                    {
                        return s.clone();
                    }
                }
            }
        }
        if self.block_visitor.bv.check_for_errors {
            let warning = self.block_visitor.bv.cv.session.struct_span_warn(
                self.block_visitor.bv.current_span,
                "this argument should be a string literal, do not call this function directly",
            );
            self.block_visitor.bv.emit_diagnostic(warning);
        }
        Rc::from("dummy argument")
    }

    /// Extract the tag kind and the propagation set from the generic arg of the function call
    /// underlying `add_tag!` or `has_tag!`. The tag type should be the second generic argument
    /// of the current function call. The tag type itself should also be parameterized, and its
    /// first type parameter should be a constant of type `TagPropagationSet`, which represents
    /// the propagation set. Return a pair of the name of the tag type, as well as the propagation
    /// set if the tag-related functions are called correctly, otherwise return `None`.
    #[logfn_inputs(TRACE)]
    fn extract_tag_kind_and_propagation_set(&mut self) -> Option<Tag> {
        precondition!(
            self.callee_known_name == KnownNames::MiraiAddTag
                || self.callee_known_name == KnownNames::MiraiHasTag
                || self.callee_known_name == KnownNames::MiraiDoesNotHaveTag
        );

        match self.callee_generic_arguments {
            None => assume_unreachable!(
                "expected tag-related function calls to have two generic arguments"
            ),
            Some(rustc_gen_args) => {
                checked_assume!(rustc_gen_args.len() == 2);

                // The second generic argument of the function call is the tag type.
                let tag_rustc_type;
                match rustc_gen_args[1].unpack() {
                    GenericArgKind::Type(rustc_type) => tag_rustc_type = rustc_type,
                    _ => {
                        // The rust type checker should ensure that the second generic argument is a type.
                        assume_unreachable!(
                            "expected the second generic argument of tag-related function calls to be a type"
                        );
                    }
                }

                // The tag type should be a generic ADT whose first parameter is a constant.
                let tag_adt_def;
                let tag_substs_ref;
                match tag_rustc_type.kind() {
                    TyKind::Adt(adt_def, substs_ref) if substs_ref.len() > 0 => {
                        tag_adt_def = adt_def;
                        tag_substs_ref = substs_ref;
                    }
                    _ => {
                        if self.block_visitor.bv.check_for_errors {
                            let err = self.block_visitor.bv.cv.session.struct_span_err(
                                self.block_visitor.bv.current_span,
                                "the tag type should be a generic type whose first parameter is a constant of type TagPropagationSet",
                            );
                            self.block_visitor.bv.emit_diagnostic(err);
                        }
                        return None;
                    }
                }

                // Extract the tag type's first parameter.
                let tag_propagation_set_rustc_const;
                match tag_substs_ref[0].unpack() {
                    GenericArgKind::Const(rustc_const)
                        if *rustc_const.ty.kind() == TyKind::Uint(ast::UintTy::U128) =>
                    {
                        tag_propagation_set_rustc_const = rustc_const
                    }
                    _ => {
                        if self.block_visitor.bv.check_for_errors {
                            let err = self.block_visitor.bv.cv.session.struct_span_err(
                                self.block_visitor.bv.current_span,
                                "the first parameter of the tag type should have type TagPropagationSet"
                            );
                            self.block_visitor.bv.emit_diagnostic(err);
                        }
                        return None;
                    }
                }

                // Analyze the tag type's first parameter to obtain a compile-time constant.
                let tag_propagation_set_value = self
                    .block_visitor
                    .visit_constant(None, tag_propagation_set_rustc_const);
                if let Expression::CompileTimeConstant(ConstantDomain::U128(data)) =
                    &tag_propagation_set_value.expression
                {
                    let tag = Tag {
                        def_id: tag_adt_def.did.into(),
                        prop_set: *data,
                    };

                    // Record the tag if it is the constant-time verification tag.
                    self.check_and_record_constant_time_verification_tag(tag_adt_def.did, &tag);

                    Some(tag)
                } else {
                    // We have already checked that `tag_propagation_set_rustc_const.ty.kind()` is
                    // `TyKind::Uint(ast::UintTy::U128)`, so the extracted compile-time constant
                    // must be `ConstantDomain::U128(..)`.
                    assume_unreachable!(
                        "expected the constant generic arg to be a compile-time constant"
                    );
                }
            }
        }
    }

    /// Check if `tag` whose def id is `tag_def_id` is the constant-time verification tag specified
    /// by the user. If so, record the tag in the current crate visitor.
    #[logfn_inputs(TRACE)]
    fn check_and_record_constant_time_verification_tag(&mut self, tag_def_id: DefId, tag: &Tag) {
        if self.block_visitor.bv.cv.constant_time_tag_cache.is_none() {
            let matched = self
                .block_visitor
                .bv
                .cv
                .options
                .constant_time_tag_name
                .as_ref()
                .map_or(false, |expected_tag_name| {
                    expected_tag_name.eq(&self.block_visitor.bv.tcx.def_path_str(tag_def_id))
                });
            if matched {
                self.block_visitor.bv.cv.constant_time_tag_cache = Some(*tag);
            }
        }
    }
}
