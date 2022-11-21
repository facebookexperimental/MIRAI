// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use std::collections::HashMap;
use std::fmt::{Debug, Formatter, Result};
use std::rc::Rc;

use log_derive::*;

use mirai_annotations::*;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty::subst::{GenericArg, GenericArgKind, SubstsRef};
use rustc_middle::ty::{Ty, TyKind, UintTy};
use rustc_target::abi::VariantIdx;

use crate::abstract_value::{AbstractValue, AbstractValueTrait};
use crate::block_visitor::BlockVisitor;
use crate::body_visitor::BodyVisitor;
use crate::constant_domain::{ConstantDomain, FunctionReference};
use crate::environment::Environment;
use crate::expression::{Expression, ExpressionType, LayoutSource};
use crate::k_limits;
use crate::known_names::KnownNames;
use crate::options::DiagLevel;
use crate::path::{Path, PathEnum, PathRefinement, PathRoot, PathSelector};
use crate::summaries::{Precondition, Summary};
use crate::tag_domain::Tag;
use crate::type_visitor::TypeVisitor;
use crate::{abstract_value, utils};

pub struct CallVisitor<'call, 'block, 'analysis, 'compilation, 'tcx> {
    pub actual_args: Vec<(Rc<Path>, Rc<AbstractValue>)>,
    pub actual_argument_types: Vec<Ty<'tcx>>,
    pub block_visitor: &'call mut BlockVisitor<'block, 'analysis, 'compilation, 'tcx>,
    pub callee_def_id: DefId,
    pub callee_func_ref: Option<Rc<FunctionReference>>,
    pub callee_fun_val: Rc<AbstractValue>,
    pub callee_generic_arguments: Option<SubstsRef<'tcx>>,
    pub callee_known_name: KnownNames,
    pub callee_generic_argument_map: Option<HashMap<rustc_span::Symbol, GenericArg<'tcx>>>,
    pub cleanup: Option<mir::BasicBlock>,
    pub destination: mir::Place<'tcx>,
    pub target: Option<mir::BasicBlock>,
    pub environment_before_call: Environment,
    pub function_constant_args: &'call [(Rc<Path>, Ty<'tcx>, Rc<AbstractValue>)],
    pub initial_type_cache: Option<Rc<HashMap<Rc<Path>, Ty<'tcx>>>>,
}

impl<'call, 'block, 'analysis, 'compilation, 'tcx> Debug
    for CallVisitor<'call, 'block, 'analysis, 'compilation, 'tcx>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "CallVisitor".fmt(f)
    }
}

impl<'call, 'block, 'analysis, 'compilation, 'tcx>
    CallVisitor<'call, 'block, 'analysis, 'compilation, 'tcx>
{
    pub(crate) fn new(
        block_visitor: &'call mut BlockVisitor<'block, 'analysis, 'compilation, 'tcx>,
        callee_def_id: DefId,
        callee_generic_arguments: Option<SubstsRef<'tcx>>,
        callee_generic_argument_map: Option<HashMap<rustc_span::Symbol, GenericArg<'tcx>>>,
        environment_before_call: Environment,
        func_const: ConstantDomain,
    ) -> CallVisitor<'call, 'block, 'analysis, 'compilation, 'tcx> {
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
                actual_args: vec![],
                actual_argument_types: vec![],
                cleanup: None,
                destination: mir::Place::return_place(),
                target: None,
                environment_before_call,
                function_constant_args: &[],
                initial_type_cache: None,
            }
        } else {
            unreachable!("caller should supply a constant function")
        }
    }

    pub fn type_visitor(&self) -> &TypeVisitor<'tcx> {
        self.block_visitor.bv.type_visitor()
    }

    pub fn type_visitor_mut(&mut self) -> &mut TypeVisitor<'tcx> {
        self.block_visitor.bv.type_visitor_mut()
    }

    /// Summarize the referenced function, specialized by its generic arguments and the actual
    /// values of any function parameters. Then cache it.
    #[logfn_inputs(TRACE)]
    pub fn create_and_cache_function_summary(
        &mut self,
        func_args: &Option<Rc<Vec<Rc<FunctionReference>>>>,
        initial_type_cache: &Option<Rc<HashMap<Rc<Path>, Ty<'tcx>>>>,
    ) -> Summary {
        let func_type = self.block_visitor.bv.tcx.type_of(self.callee_def_id);
        trace!("summarizing {:?}: {:?}", self.callee_def_id, func_type);
        let tcx = self.block_visitor.bv.tcx;
        if tcx.is_mir_available(self.callee_def_id) {
            let mut body_visitor = BodyVisitor::new(
                self.block_visitor.bv.cv,
                self.callee_def_id,
                self.block_visitor.bv.buffered_diagnostics,
                self.block_visitor.bv.active_calls_map,
                self.block_visitor.bv.cv.type_cache.clone(),
            );
            body_visitor.treat_as_foreign = self.block_visitor.bv.treat_as_foreign
                || self.block_visitor.bv.assume_preconditions_of_next_call;
            body_visitor.type_visitor_mut().actual_argument_types =
                self.actual_argument_types.clone();
            body_visitor.type_visitor_mut().generic_arguments = self.callee_generic_arguments;
            body_visitor.type_visitor_mut().generic_argument_map =
                self.callee_generic_argument_map.clone();
            body_visitor.analyzing_static_var = self.block_visitor.bv.analyzing_static_var;
            if let Some(cache) = &self.initial_type_cache {
                for (p, t) in cache.iter() {
                    body_visitor
                        .type_visitor_mut()
                        .set_path_rustc_type(p.clone(), *t);
                }
            }
            let mut summary = body_visitor.visit_body(self.function_constant_args);
            trace!("summary {:?} {:?}", self.callee_def_id, summary);
            if let Some(func_ref) = &self.callee_func_ref {
                // If there is already a computed summary in the cache, we are in a recursive loop
                // and hence have to join the summaries.
                let previous_summary = self
                    .block_visitor
                    .bv
                    .cv
                    .summary_cache
                    .get_summary_for_call_site(func_ref, func_args, initial_type_cache);
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
                    .set_summary_for_call_site(
                        func_ref,
                        func_args,
                        initial_type_cache,
                        summary.clone(),
                    );
            }
            return summary;
        }
        if !self.block_visitor.bv.tcx.is_static(self.callee_def_id)
            && self.callee_known_name != KnownNames::StdCloneClone
        {
            info!("function {:?} has no MIR", self.callee_def_id);
            if let Some(fr) = &self.callee_func_ref {
                info!(
                    "summary key {:?} with signature {:?}",
                    fr.summary_cache_key, fr.argument_type_key
                );
            }
        }
        Summary::default()
    }

    /// If self.callee_def_id is a trait (virtual) then this tries to get the def_id of the
    /// concrete method that implements the given virtual method and returns the summary of that,
    /// computing it if necessary.
    #[logfn_inputs(TRACE)]
    fn try_to_devirtualize(&mut self) {
        let tcx = self.block_visitor.bv.tcx;
        if self
            .block_visitor
            .bv
            .tcx
            .is_mir_available(self.callee_def_id)
            && !utils::is_trait_method(self.callee_def_id, tcx)
        {
            return;
        }
        if let Some(gen_args) = self.callee_generic_arguments {
            // The parameter environment of the caller provides a resolution context for the callee.
            let param_env = rustc_middle::ty::ParamEnv::reveal_all();
            trace!(
                "devirtualize resolving def_id {:?}: {:?}",
                self.callee_def_id,
                tcx.type_of(self.callee_def_id)
            );
            trace!("devirtualize resolving func_ref {:?}", self.callee_func_ref,);
            trace!("gen_args {:?}", gen_args);
            if let Some(arg0_ty) = gen_args.types().next() {
                if matches!(arg0_ty.kind(), TyKind::Dynamic(..)) {
                    // Instance::resolve panics if it can't find a vtable entry for the given def_id
                    // It is hard to figure out exactly when this will be the case, but it does
                    // happen in a case where the first generic argument type is Dynamic.
                    return;
                }
            }
            let abi = tcx.type_of(self.callee_def_id).fn_sig(tcx).abi();
            let resolved_instance = if abi == rustc_target::spec::abi::Abi::Rust {
                Some(rustc_middle::ty::Instance::resolve(
                    tcx,
                    param_env,
                    self.callee_def_id,
                    gen_args,
                ))
            } else {
                None
            };
            if let Some(Ok(Some(instance))) = resolved_instance {
                let resolved_def_id = instance.def.def_id();
                let tcx = tcx;
                let has_mir = tcx.is_mir_available(resolved_def_id);
                if !has_mir && self.callee_known_name == KnownNames::StdCloneClone {
                    return;
                }
                self.callee_def_id = resolved_def_id;
                let resolved_ty = tcx.type_of(resolved_def_id);
                let resolved_map = self.type_visitor().get_generic_arguments_map(
                    resolved_def_id,
                    instance.substs,
                    &[],
                );
                let specialized_resolved_ty = self
                    .type_visitor()
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
                        Some(instance.substs),
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
                self.callee_generic_argument_map = self.type_visitor().get_generic_arguments_map(
                    resolved_def_id,
                    instance.substs,
                    &self.actual_argument_types,
                );
                if has_mir && specialized_resolved_ty.is_closure() {
                    let mir = tcx.optimized_mir(resolved_def_id);
                    if self.actual_argument_types.len() + 1 == mir.arg_count {
                        // When the closure has no captured variables, the first argument is just the function pointer.
                        // Sadly, MIR omits this argument (because the call is via a trait), so we have to add it here.
                        self.actual_args
                            .insert(0, (Path::new_parameter(1), self.callee_fun_val.clone()));
                        self.actual_argument_types.insert(
                            0,
                            tcx.mk_mut_ref(tcx.lifetimes.re_static, specialized_resolved_ty),
                        );
                    }
                }
            } else {
                debug!(
                    "could not resolve function {:?}, {:?}, {:?}",
                    self.callee_def_id, param_env, gen_args,
                )
            }
        }
    }

    /// Extract a list of function references from an environment of function constant arguments
    #[logfn_inputs(TRACE)]
    fn get_function_constant_signature(
        &mut self,
        func_args: &[(Rc<Path>, Ty<'tcx>, Rc<AbstractValue>)],
    ) -> Option<Rc<Vec<Rc<FunctionReference>>>> {
        if func_args.is_empty() {
            return None;
        }
        let vec: Vec<Rc<FunctionReference>> = func_args
            .iter()
            .filter_map(|(_, _, v)| self.block_visitor.get_func_ref(v))
            .collect();
        if vec.is_empty() {
            return None;
        }
        Some(Rc::new(vec))
    }

    /// Returns a summary of the function to call, obtained from the summary cache.
    #[logfn_inputs(TRACE)]
    pub fn get_function_summary(&mut self) -> Option<Summary> {
        self.try_to_devirtualize();
        if self.block_visitor.bv.cv.call_graph.needs_edges() {
            if self.actual_argument_types.is_empty() {
                self.block_visitor.bv.cv.call_graph.add_edge(
                    self.block_visitor.bv.def_id,
                    self.callee_def_id,
                    "".to_string().into_boxed_str(),
                );
            } else {
                for ty in self.actual_argument_types.iter() {
                    self.block_visitor.bv.cv.call_graph.add_edge(
                        self.block_visitor.bv.def_id,
                        self.callee_def_id,
                        ty.to_string().into_boxed_str(),
                    );
                }
            }
        }
        if let Some(func_ref) = &self.callee_func_ref.clone() {
            // If the actual arguments include any function constants, collect them together
            // and pass them to get_summary_for_function_constant so that their signatures
            // can be included in the type specific key that is used to look up non generic
            // predefined summaries.

            let func_args = self.get_function_constant_signature(self.function_constant_args);
            let tcx = self.block_visitor.bv.tcx;
            let callee_defid = func_ref.def_id.unwrap_or(self.callee_def_id);
            self.block_visitor.bv.cv.call_graph.add_call_site(
                self.block_visitor.bv.current_span,
                self.block_visitor.bv.def_id,
                callee_defid,
                !tcx.is_mir_available(callee_defid)
                    || (!callee_defid.is_local()
                        && (self.callee_generic_arguments.is_none()
                            || self
                                .callee_generic_arguments
                                .unwrap()
                                .types()
                                .next()
                                .is_none())
                        && func_args.is_none()),
            );
            let initial_type_cache = self.initial_type_cache.clone();
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
                .get_summary_for_call_site(func_ref, &func_args, &initial_type_cache)
                .clone();
            if result.is_computed || func_ref.def_id.is_none() {
                return Some(result);
            }
            if call_depth < 3 {
                let mut summary =
                    self.create_and_cache_function_summary(&func_args, &initial_type_cache);
                if call_depth >= 1 {
                    summary.post_condition = None;

                    // Widen summary at call level 1 so that the level 0 call sees the widened values.
                    if call_depth == 1 {
                        summary.widen_side_effects();
                    }
                    self.block_visitor
                        .bv
                        .cv
                        .summary_cache
                        .set_summary_for_call_site(
                            func_ref,
                            &func_args,
                            &self.initial_type_cache,
                            summary.clone(),
                        );
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
                self.block_visitor
                    .bv
                    .cv
                    .summary_cache
                    .set_summary_for_call_site(
                        func_ref,
                        &func_args,
                        &self.initial_type_cache,
                        summary.clone(),
                    );
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
        checked_assume!(self.actual_args.len() == 1);
        let target_type = ExpressionType::from(
            self.type_visitor()
                .get_dereferenced_type(self.actual_argument_types[0])
                .kind(),
        );
        let source_path = Path::new_deref(self.actual_args[0].0.clone(), target_type)
            .canonicalize(&self.block_visitor.bv.current_environment);
        let target_type = self
            .type_visitor()
            .get_rustc_place_type(&self.destination, self.block_visitor.bv.current_span);
        let target_path = self.block_visitor.visit_rh_place(&self.destination);
        if !summary.is_computed {
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
                    .update_value_at(target_path, value.clone());
            }
        }
        self.use_entry_condition_as_exit_condition();
    }

    /// If the current call is to a well known function for which we don't have a cached summary,
    /// this function will update the environment as appropriate and return true. If the return
    /// result is false, just carry on with the normal logic.
    #[logfn_inputs(TRACE)]
    pub fn handled_as_special_function_call(&mut self) -> bool {
        match self.callee_known_name {
            KnownNames::StdCloneClone => {
                checked_assume!(self.actual_argument_types.len() == 1);
                return self.handled_clone();
            }
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
                self.use_entry_condition_as_exit_condition();
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
                let target_path = self.block_visitor.visit_rh_place(&self.destination);
                let target_rustc_type = self
                    .type_visitor()
                    .get_rustc_place_type(&self.destination, self.block_visitor.bv.current_span);
                let return_value_path = Path::new_result();
                let return_value = self
                    .block_visitor
                    .bv
                    .lookup_path_and_refine_result(return_value_path, target_rustc_type);
                self.block_visitor
                    .bv
                    .update_value_at(target_path, return_value);
                self.use_entry_condition_as_exit_condition();
                return true;
            }
            KnownNames::MiraiVerify => {
                checked_assume!(self.actual_args.len() == 2);
                if self.block_visitor.bv.check_for_errors {
                    self.report_calls_to_special_functions();
                }
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
                let mut block_visitor = BlockVisitor::new(self.block_visitor.bv);
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
            KnownNames::StdPanickingAssertFailed
            | KnownNames::StdPanickingBeginPanic
            | KnownNames::StdPanickingBeginPanicFmt => {
                if self.block_visitor.bv.check_for_errors {
                    self.report_calls_to_special_functions();
                }
                if let Some(target) = &self.cleanup {
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
                return true;
            }
            _ => {
                let result = self.try_to_inline_special_function();
                if !result.is_bottom() {
                    let target_path = self.block_visitor.visit_lh_place(&self.destination);
                    self.block_visitor.bv.update_value_at(target_path, result);
                    self.use_entry_condition_as_exit_condition();
                    return true;
                }
            }
        }
        false
    }

    /// If the self parameter is &std::Option::None, the call to std::Clone::clone
    /// can be handled without resolving the trait method to a concrete method.
    #[logfn_inputs(TRACE)]
    fn handled_clone(&mut self) -> bool {
        precondition!(self.actual_argument_types.len() == 1);
        if let TyKind::Ref(_, t, _) = self.actual_argument_types[0].kind() {
            if let TyKind::Adt(def, substs) = t.kind() {
                if def.variants().is_empty() {
                    return false;
                }
                let variant_0 = VariantIdx::from_u32(0);
                if Some(def.variants()[variant_0].def_id)
                    == self.block_visitor.bv.tcx.lang_items().option_none_variant()
                {
                    let target_path_discr = Path::new_discriminant(
                        self.block_visitor.visit_rh_place(&self.destination),
                    );
                    let arg0_discr_path = Path::new_discriminant(
                        Path::new_deref(
                            self.actual_args[0].0.clone(),
                            ExpressionType::NonPrimitive,
                        )
                        .canonicalize(&self.block_visitor.bv.current_environment),
                    );
                    let discr_ty = t.discriminant_ty(self.block_visitor.bv.tcx);
                    let discr_0_val = self.block_visitor.get_int_const_val(0, discr_ty);
                    let discr_val = self
                        .block_visitor
                        .bv
                        .lookup_path_and_refine_result(arg0_discr_path, discr_ty);
                    let is_zero = discr_val.equals(discr_0_val.clone());
                    let target_discr_value = match is_zero.as_bool_if_known() {
                        Some(false) => {
                            // Have to clone the Some(..) variant, let visit_caller take care of that
                            return false;
                        }
                        Some(true) => {
                            // Cloning is just copying the discriminant value
                            discr_0_val
                        }
                        None => {
                            // Might have to clone the Some(..) variant, so can't be handled here,
                            if let Some(promotable_is_zero) =
                                is_zero.extract_promotable_disjuncts(false)
                            {
                                // The caller might be able to avoid the diagnostic because it
                                // knows the actual argument whereas here we only know the type.
                                let specialized_substs = self
                                    .type_visitor()
                                    .specialize_substs(substs, &self.callee_generic_argument_map);
                                if !utils::are_concrete(specialized_substs) {
                                    // The clone method will not resolve, but we don't want visit_caller
                                    // to issue a diagnostic because is_zero might refine to true
                                    // further up the call stack. We deal with this by adding a
                                    // precondition to the current function requiring that the
                                    // caller (or on its callers) must ensure that is_zero will be true
                                    // at runtime when this call is issued.
                                    let precondition = Precondition {
                                            condition: promotable_is_zero,
                                            message: Rc::from("incomplete analysis of call because of failure to resolve std::Clone::clone method"),
                                            provenance: None,
                                            spans: vec![self.block_visitor.bv.current_span.source_callsite()],
                                        };
                                    self.block_visitor.bv.preconditions.push(precondition);
                                    discr_0_val
                                } else {
                                    // let visit_call issue a diagnostic
                                    return false;
                                }
                            } else {
                                // let visit_call resolve the clone method and deal with it
                                return false;
                            }
                        }
                    };
                    self.block_visitor
                        .bv
                        .update_value_at(target_path_discr, target_discr_value);
                    self.use_entry_condition_as_exit_condition();
                    return true;
                } else {
                    return false;
                }
            }
        }
        false
    }

    /// Use this for terminators that deterministically transfer control to a single successor block.
    /// Such blocks, obviously, do not alter their entry path condition.
    #[logfn_inputs(TRACE)]
    fn use_entry_condition_as_exit_condition(&mut self) {
        if let Some(target) = &self.target {
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

                // If we never get here, rather call verify_unreachable!()
                if !entry_cond_as_bool.unwrap_or(true) {
                    let span = self.block_visitor.bv.current_span.source_callsite();
                    let message =
                        "this is unreachable, mark it as such by using the verify_unreachable! macro";
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
                    "assumption is provably false and it will be ignored"
                } else {
                    return;
                };
                let span = self.block_visitor.bv.current_span.source_callsite();
                let warning = self
                    .block_visitor
                    .bv
                    .cv
                    .session
                    .struct_span_warn(span, message);
                self.block_visitor.bv.emit_diagnostic(warning);
            }
            KnownNames::MiraiPostcondition => {
                let actual_args = self.actual_args.clone();
                assume!(actual_args.len() == 3); // The type checker ensures this.
                let (_, assumption) = &actual_args[1];
                let (_, cond) = &actual_args[0];
                if !assumption.as_bool_if_known().unwrap_or(false) {
                    // Not an assumed post condition, so check the condition and only add this to
                    // the summary if it is reachable and true.
                    let message = self.coerce_to_string(&actual_args[2].0.clone());
                    if self
                        .block_visitor
                        .check_special_function_condition(
                            cond,
                            message.as_ref(),
                            KnownNames::MiraiPostcondition,
                        )
                        .is_none()
                    {
                        self.block_visitor.try_extend_post_condition(cond);
                    }
                } else {
                    self.block_visitor.try_extend_post_condition(cond);
                }
            }
            KnownNames::MiraiVerify => {
                let actual_args = self.actual_args.clone();
                assume!(actual_args.len() == 2); // The type checker ensures this.
                let (_, cond) = &actual_args[0];
                let message = self.coerce_to_string(&actual_args[1].0);
                self.block_visitor.check_special_function_condition(
                    cond,
                    message.as_ref(),
                    KnownNames::MiraiVerify,
                );
            }
            KnownNames::StdPanickingAssertFailed
            | KnownNames::StdPanickingBeginPanic
            | KnownNames::StdPanickingBeginPanicFmt => {
                assume!(!self.actual_args.is_empty()); // The type checker ensures this.
                let mut path_cond = self.block_visitor.might_be_reachable();
                if !path_cond.unwrap_or(true) {
                    // We never get to this call, so nothing to report.
                    return;
                }
                let msg = match self.callee_known_name {
                    KnownNames::StdPanickingAssertFailed => Rc::from("assertion failed"),
                    KnownNames::StdPanickingBeginPanic => {
                        self.coerce_to_string(&self.actual_args[0].0.clone())
                    }
                    _ => {
                        let arguments_struct_path = self.actual_args[0].0.clone();
                        let pieces_path_fat = Path::new_field(arguments_struct_path.clone(), 0)
                            .canonicalize(&self.block_visitor.bv.current_environment);
                        let pieces_path_thin = Path::new_field(pieces_path_fat.clone(), 0);
                        let pieces_path_len = Path::new_length(pieces_path_fat);
                        let len_val = self.block_visitor.bv.lookup_path_and_refine_result(
                            pieces_path_len,
                            self.block_visitor.bv.tcx.types.usize,
                        );
                        let len = if let Expression::CompileTimeConstant(ConstantDomain::U128(v)) =
                            &len_val.expression
                        {
                            *v
                        } else {
                            1u128
                        };
                        let args_path_fat = Path::new_field(arguments_struct_path, 2)
                            .canonicalize(&self.block_visitor.bv.current_environment);
                        let args_path_len = Path::new_length(args_path_fat);
                        let arg_len_val = self.block_visitor.bv.lookup_path_and_refine_result(
                            args_path_len,
                            self.block_visitor.bv.tcx.types.usize,
                        );
                        let num_args =
                            if let Expression::CompileTimeConstant(ConstantDomain::U128(v)) =
                                &arg_len_val.expression
                            {
                                *v
                            } else {
                                1u128
                            };

                        let mut msg = String::new();
                        for i in 0..len {
                            let index = Rc::new(i.into());
                            let piece_path_fat = Path::new_index(pieces_path_thin.clone(), index)
                                .canonicalize(&self.block_visitor.bv.current_environment);
                            msg += self.coerce_to_string(&piece_path_fat).as_ref();
                            if i < num_args {
                                msg += "{}";
                                // todo: attach arg value to precondition and let caller refine them
                                // and turn them into strings suitable for display in the diagnostics
                            }
                        }
                        Rc::from(msg)
                    }
                };
                if msg.contains("entered unreachable code")
                    || msg.contains("not yet implemented")
                    || msg.contains("not implemented")
                    || msg.starts_with("unrecoverable: ")
                    || (msg.starts_with("assertion failed")
                        && self.block_visitor.bv.cv.options.test_only)
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

                let span = self.block_visitor.bv.current_span.source_callsite();

                if path_cond.unwrap_or(false)
                    && self.block_visitor.bv.function_being_analyzed_is_root()
                {
                    // We always get to this call and we have to assume that the function will
                    // get called, so keep the message certain.
                    // Don't, however, complain about panics in the standard contract summaries
                    if std::env::var("MIRAI_START_FRESH").is_err() {
                        let warning = self
                            .block_visitor
                            .bv
                            .cv
                            .session
                            .struct_span_warn(span, msg.as_ref());
                        self.block_visitor.bv.emit_diagnostic(warning);
                    } else {
                        // If we see an unconditional panic inside a standard contract summary,
                        // make it into an unsatisfiable precondition.
                        let precondition = Precondition {
                            condition: Rc::new(abstract_value::FALSE),
                            message: msg,
                            provenance: None,
                            spans: vec![],
                        };
                        self.block_visitor.bv.preconditions.push(precondition);
                    }
                } else {
                    // We might get to this call, depending on the state at the call site.
                    //
                    if msg.contains("Post-condition of ") || msg.contains("Invariant of ") {
                        // Dealing with contracts crate
                        if self.block_visitor.bv.function_being_analyzed_is_root() {
                            let msg = msg.replace(" violated", " possibly violated");
                            let warning = self
                                .block_visitor
                                .bv
                                .cv
                                .session
                                .struct_span_warn(span, msg.as_str());
                            self.block_visitor.bv.emit_diagnostic(warning);
                        }
                        return;
                    }

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
                    if let Some(promotable_entry_condition) = self
                        .block_visitor
                        .bv
                        .current_environment
                        .entry_condition
                        .extract_promotable_conjuncts(false)
                    {
                        let condition = promotable_entry_condition.logical_not();
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
                    } else {
                        // If the assertion cannot be promoted because the caller cannot
                        // satisfy it (because it contains a reference to local variable),
                        // then we need to produce a diagnostic after all, but only if this
                        // a local function (i.e. a function in the crate being analyzed).
                        if self.block_visitor.bv.def_id.is_local() {
                            let warning = self
                                .block_visitor
                                .bv
                                .cv
                                .session
                                .struct_span_warn(span, msg.as_ref());
                            self.block_visitor.bv.emit_diagnostic(warning);
                        } else {
                            // Since the assertion occurs in code that is being used rather than
                            // analyzed, we'll assume that the code is correct and the analyzer
                            // discovered a false positive.
                        }
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
                let arg_type = ExpressionType::from(self.actual_argument_types[0].kind());
                let bit_length = arg_type.bit_length();
                self.actual_args[0]
                    .1
                    .intrinsic_bit_vector_unary(bit_length, self.callee_known_name)
            }
            KnownNames::StdIntrinsicsCtlzNonzero | KnownNames::StdIntrinsicsCttzNonzero => {
                checked_assume!(self.actual_args.len() == 1);
                if self.block_visitor.bv.check_for_errors {
                    let non_zero = self.actual_args[0].1.not_equals(Rc::new(0u128.into()));
                    if let Some(warning) = self.block_visitor.check_special_function_condition(
                        &non_zero,
                        "argument is zero",
                        self.callee_known_name,
                    ) {
                        // The condition may be reachable and false. Promote it to a precondition if possible.
                        match (
                            self.block_visitor
                                .bv
                                .current_environment
                                .entry_condition
                                .extract_promotable_conjuncts(false),
                            non_zero.extract_promotable_disjuncts(false),
                        ) {
                            (Some(promotable_entry_condition), Some(promotable_non_zero))
                                if self.block_visitor.bv.preconditions.len()
                                    < k_limits::MAX_INFERRED_PRECONDITIONS =>
                            {
                                let condition = promotable_entry_condition
                                    .logical_not()
                                    .or(promotable_non_zero);
                                let precondition = Precondition {
                                    condition,
                                    message: warning,
                                    provenance: None,
                                    spans: vec![self.block_visitor.bv.current_span],
                                };
                                self.block_visitor.bv.preconditions.push(precondition);
                            }
                            _ => {
                                let warning = self.block_visitor.bv.cv.session.struct_span_warn(
                                    self.block_visitor.bv.current_span,
                                    warning.as_ref(),
                                );
                                self.block_visitor.bv.emit_diagnostic(warning);
                            }
                        }
                    }
                }
                let arg_type = ExpressionType::from(self.actual_argument_types[0].kind());
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
            KnownNames::StdIntrinsicsNeedsDrop => self.handle_needs_drop(),
            KnownNames::StdIntrinsicsOffset => self.handle_offset(),
            KnownNames::StdIntrinsicsRawEq => self.handle_raw_eq(),
            KnownNames::StdIntrinsicsSizeOf => self.handle_size_of(),
            KnownNames::StdIntrinsicsSizeOfVal => self.handle_size_of_val(),
            KnownNames::StdSliceCmpMemcmp => self.handle_memcmp(),
            _ => abstract_value::BOTTOM.into(),
        }
    }

    /// Fn::call, FnMut::call_mut, FnOnce::call_once all receive two arguments:
    /// 1. A function pointer or closure instance to call.
    /// 2. A tuple of argument values for the call.
    /// The tuple is unpacked and the callee is then invoked with its normal function signature.
    /// In the case of calling a closure, the closure signature includes the closure as the first argument.
    ///
    /// Sync::Once::call_once receives two arguments
    /// 1. A self pointer to the Once object
    /// 2. The closure instance to call.
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
        let callee_func_ref = self.block_visitor.get_func_ref(&callee);

        // Get the path of the tuple containing the arguments.
        let callee_arg_array_path = self.actual_args[1].0.clone();
        if let Some(func_ref) = &callee_func_ref {
            let def_id = func_ref.def_id.expect("defined when used here");
            let func_const = ConstantDomain::Function(func_ref.clone());

            // Unpack the type of the second argument, which should be a tuple.
            checked_assume!(self.actual_argument_types.len() == 2);
            let mut actual_argument_types: Vec<Ty<'tcx>> =
                if let TyKind::Tuple(tuple_types) = self.actual_argument_types[1].kind() {
                    tuple_types.iter().collect()
                } else {
                    assume_unreachable!("expected second type argument to be a tuple type");
                };

            // Unpack the second argument, which should be a tuple
            let mut actual_args: Vec<(Rc<Path>, Rc<AbstractValue>)> = actual_argument_types
                .iter()
                .enumerate()
                .map(|(i, t)| {
                    let arg_path = Path::new_field(callee_arg_array_path.clone(), i)
                        .canonicalize(&self.block_visitor.bv.current_environment);
                    let arg_val = self
                        .block_visitor
                        .bv
                        .lookup_path_and_refine_result(arg_path.clone(), *t);
                    (arg_path, arg_val)
                })
                .collect();

            // Prepend the callee closure/generator/function to the unpacked arguments vector
            // if the called function actually expects it.
            let tcx = self.block_visitor.bv.tcx;
            let callee_ty = self.actual_argument_types[0];
            if !callee_ty.is_fn() || tcx.is_closure(def_id) {
                actual_args.insert(0, self.actual_args[0].clone());
                actual_argument_types.insert(0, callee_ty);
                if self.callee_known_name == KnownNames::StdOpsFunctionFnOnceCallOnce
                    && self.block_visitor.bv.tcx.is_mir_available(def_id)
                {
                    // call_once consumes it's callee argument. If the callee does not,
                    // we have to provide it with a reference.
                    // Sadly, the easiest way to get hold of the type of the first parameter
                    // of the callee is to look at its MIR body. If there is no body, we wont
                    // be executing it and the type of the first argument is immaterial, so this
                    // does not cause problems.
                    let mir = tcx.optimized_mir(def_id);
                    if let Some(decl) = mir.local_decls.get(mir::Local::from(1usize)) {
                        if decl.ty.is_ref() {
                            let closure_path = self.actual_args[0].0.clone();
                            let closure_reference = AbstractValue::make_reference(closure_path);
                            actual_args[0] = (
                                Path::get_as_path(closure_reference.clone()),
                                closure_reference,
                            );
                            // decl.ty is not type specialized
                            actual_argument_types[0] =
                                tcx.mk_mut_ref(tcx.lifetimes.re_static, callee_ty);
                        }
                    }
                }
            }

            let function_constant_args = self
                .block_visitor
                .get_function_constant_args(&actual_args, &actual_argument_types);

            // Get the generic argument map for the indirectly called function
            let generic_arguments = match callee_ty.kind() {
                TyKind::Closure(_, substs) => Some(self.type_visitor().specialize_substs(
                    substs.as_closure().substs,
                    &self.type_visitor().generic_argument_map,
                )),
                TyKind::Generator(_, substs, _) => Some(self.type_visitor().specialize_substs(
                    substs.as_generator().substs,
                    &self.type_visitor().generic_argument_map,
                )),
                TyKind::FnDef(_, substs) | TyKind::Opaque(_, substs) => Some(
                    self.type_visitor()
                        .specialize_substs(substs, &self.type_visitor().generic_argument_map),
                ),
                _ => self.block_visitor.bv.cv.substs_cache.get(&def_id).cloned(),
            };

            let argument_map = if let Some(substs) = generic_arguments {
                self.type_visitor().get_generic_arguments_map(
                    def_id,
                    substs,
                    &actual_argument_types,
                )
            } else {
                None
            };

            // Set up a call visitor
            let environment_before_call = self.block_visitor.bv.current_environment.clone();
            let mut block_visitor = BlockVisitor::new(self.block_visitor.bv);
            let mut indirect_call_visitor = CallVisitor::new(
                &mut block_visitor,
                def_id,
                generic_arguments,
                argument_map,
                environment_before_call,
                func_const,
            );
            indirect_call_visitor.actual_args = actual_args;
            indirect_call_visitor.actual_argument_types = actual_argument_types;
            indirect_call_visitor.function_constant_args = &function_constant_args;
            indirect_call_visitor.callee_fun_val = callee.clone();
            indirect_call_visitor.callee_known_name = KnownNames::None;
            indirect_call_visitor.destination = self.destination;
            indirect_call_visitor.target = self.target;
            let summary = indirect_call_visitor.get_function_summary();
            if let Some(summary) = summary {
                if summary.is_computed {
                    indirect_call_visitor.transfer_and_refine_into_current_environment(&summary);
                }
                if summary.is_incomplete
                    && self
                        .block_visitor
                        .bv
                        .already_reported_errors_for_call_to
                        .insert(callee)
                {
                    let saved_callee_def_id = self.callee_def_id;
                    self.callee_def_id = def_id;
                    self.report_incomplete_summary();
                    self.callee_def_id = saved_callee_def_id;
                }
                return;
            }
        }
        if self
            .block_visitor
            .bv
            .already_reported_errors_for_call_to
            .insert(callee.clone())
        {
            debug!("unknown callee {:?}", callee);
            self.block_visitor.report_missing_summary();
        }
    }

    /// Replace the call result with an abstract value of the same type as the
    /// destination place.
    #[logfn_inputs(TRACE)]
    fn handle_abstract_value(&mut self) {
        if let Some(target) = &self.target {
            let path = self.block_visitor.visit_rh_place(&self.destination);
            let expression_type = self
                .type_visitor()
                .get_place_type(&self.destination, self.block_visitor.bv.current_span);
            let abstract_value = AbstractValue::make_typed_unknown(expression_type, path.clone());
            self.block_visitor.bv.update_value_at(path, abstract_value);
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
            let (source_path, source_rustc_type) = self.deref_tag_source();
            trace!("MiraiAddTag: tagging {:?} with {:?}", source_path, tag);

            // Check if the tagged value has a pointer type (e.g., a reference).
            // Emit an warning message if so.
            if self.block_visitor.bv.check_for_errors && source_rustc_type.is_any_ptr() {
                let warning = self.block_visitor.bv.cv.session.struct_span_warn(
                    self.block_visitor.bv.current_span,
                    "the macro add_tag! expects its argument to be a reference to a non-reference value",
                );
                self.block_visitor.bv.emit_diagnostic(warning);
            }

            // Augment the tags associated at the source with a new tag.
            self.block_visitor
                .bv
                .attach_tag_to_value_at_path(tag, source_path, source_rustc_type);
        }

        // Update exit conditions.
        self.use_entry_condition_as_exit_condition();
    }

    /// Returns a canonicalized dereferenced path to the first argument, along with the dereferenced
    /// rustc type. If the dereferenced argument is a slice pointer, or a box, then return the
    /// thin pointer path to the dereferenced value. In the case of a box, the argument path will
    /// be a reference to the box, so the dereferenced thin pointer path will be (*p).0.0.
    #[logfn_inputs(TRACE)]
    fn deref_tag_source(&mut self) -> (Rc<Path>, Ty<'tcx>) {
        precondition!(self.actual_args.len() == 1);

        let source_pointer_path = self.actual_args[0].0.clone();
        let source_pointer_rustc_type = self.actual_argument_types[0];
        let mut source_rustc_type = self
            .type_visitor()
            .get_dereferenced_type(source_pointer_rustc_type);
        let target_type = ExpressionType::from(source_rustc_type.kind());
        let source_thin_pointer_path = if source_rustc_type.is_box() {
            source_rustc_type = source_rustc_type.boxed_ty();
            let box_path = Path::new_deref(source_pointer_path, target_type)
                .canonicalize(&self.block_visitor.bv.current_environment);
            // Box.0 = Unique, Unique.0 = NonNullPtr, NonNullPtr.0 = source thin pointer
            Path::new_field(Path::new_field(Path::new_field(box_path, 0), 0), 0)
        } else if self
            .type_visitor()
            .is_slice_pointer(source_pointer_rustc_type.kind())
        {
            Path::new_field(source_pointer_path, 0)
        } else {
            source_pointer_path
        };
        let deref_path = Path::new_deref(source_thin_pointer_path, target_type)
            .canonicalize(&self.block_visitor.bv.current_environment);
        (deref_path, source_rustc_type)
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
                .clone()
        } else {
            // Give the assumed condition priority over the existing conjuncts when the and expression
            // size overflows.
            let assumed_condition =
                AbstractValue::make_from(assumed_condition.expression.clone(), 0);
            self.block_visitor
                .bv
                .current_environment
                .entry_condition
                .and(assumed_condition)
        };
        if let Some(target) = self.target {
            self.block_visitor
                .bv
                .current_environment
                .exit_conditions
                .insert_mut(target, exit_condition);
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
    #[logfn_inputs(DEBUG)]
    fn handle_check_tag(&mut self, checking_presence: bool) {
        precondition!(self.actual_args.len() == 1);
        debug!(
            "path condition {:?}",
            self.block_visitor.bv.current_environment.entry_condition
        );

        let result: Option<Rc<AbstractValue>>;
        if let Some(tag) = self.extract_tag_kind_and_propagation_set() {
            let (source_path, source_rustc_type) = self.deref_tag_source();
            debug!(
                "MiraiCheckTag: checking if {:?} has {}been tagged with {:?}",
                source_path,
                (if checking_presence { "" } else { "never " }),
                tag,
            );

            // Check if the tagged value has a pointer type (e.g., a reference).
            // Emit a warning message if so.
            if self.block_visitor.bv.check_for_errors && source_rustc_type.is_any_ptr() {
                let warning = self.block_visitor.bv.cv.session.struct_span_warn(
                    self.block_visitor.bv.current_span,
                    format!(
                        "the macro {} expects its first argument to be a reference to a non-reference value",
                        if checking_presence { "has_tag! " } else { "does_not_have_tag!" },
                    ).as_str(),
                );
                self.block_visitor.bv.emit_diagnostic(warning);
            }

            // Get the value to check for the presence or absence of the tag
            let (tag_field_path, tag_field_value) = self.get_value_to_check_for_tag(
                tag,
                checking_presence,
                source_path.clone(),
                source_rustc_type,
            );

            // Decide the result of has_tag! or does_not_have_tag!.
            let mut check_result =
                AbstractValue::make_tag_check(tag_field_value, tag, checking_presence);

            // If the tag can be propagated through sub-components we need to check the tag on the
            // values that can contain tag_field_path as a sub-component.
            // Operationally, if tag_field_path is a qualified path we check if any of its prefixes
            // has the tag (when checking_presence = true), or if all of its prefixes does not have
            // the tag (when checking_presence = false).
            if tag.is_propagated_by(TagPropagation::SubComponent) {
                let mut path_prefix = &tag_field_path;
                while let PathEnum::QualifiedPath { qualifier, .. } = &path_prefix.value {
                    debug!("qualifier {:?}", qualifier);
                    path_prefix = qualifier;

                    let path_prefix_rustc_type = self
                        .type_visitor()
                        .get_path_rustc_type(path_prefix, self.block_visitor.bv.current_span);
                    if !path_prefix_rustc_type.is_scalar() {
                        let tag_field_value = self
                            .block_visitor
                            .bv
                            .extract_tag_field_of_non_scalar_value_at(
                                path_prefix,
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

            // If the tag can be propagated from a sub-component to its container
            if tag.is_propagated_by(TagPropagation::SuperComponent) {
                let root = source_path.get_path_root();
                let value_map = self.block_visitor.bv.current_environment.value_map.clone();
                for (_, value) in value_map.iter().filter(|(p, _)| p.is_rooted_by(root)) {
                    let mut value = value.clone();
                    if let Expression::Reference(p) = &value.expression {
                        if let PathEnum::HeapBlock { .. } = &p.value {
                            let layout_field = Path::new_layout(p.clone());
                            let (_, tag_field_value) = self
                                .block_visitor
                                .bv
                                .extract_tag_field_of_non_scalar_value_at(
                                    &layout_field,
                                    self.block_visitor.bv.tcx.types.trait_object_dummy_self,
                                );
                            value = tag_field_value.clone();
                        }
                    }
                    if checking_presence {
                        // We are checking presence of a tag. It is equivalent to *any* prefix having the tag.
                        // Thus we use a logical or.
                        check_result = check_result.or(AbstractValue::make_tag_check(
                            value,
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
                            value,
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

            result = Some(check_result);
        } else {
            result = None;
        }

        // Return the abstract result and update exit conditions.
        let target_path = self.block_visitor.visit_rh_place(&self.destination);
        self.block_visitor.bv.update_value_at(
            target_path.clone(),
            result.unwrap_or_else(|| {
                AbstractValue::make_typed_unknown(ExpressionType::Bool, target_path)
            }),
        );
        self.use_entry_condition_as_exit_condition();
    }

    /// Get the possibly tagged value associated with source_path.
    /// It the value at source path is a scalar value, it will just be that value.
    /// If the value at source path is a structured value, it will be the value of its $tag field.
    #[logfn_inputs(TRACE)]
    fn get_value_to_check_for_tag(
        &mut self,
        tag: Tag,
        checking_presence: bool,
        source_path: Rc<Path>,
        source_rustc_type: Ty<'tcx>,
    ) -> (Rc<Path>, Rc<AbstractValue>) {
        if let PathEnum::Computed { value } = &source_path.value {
            match &value.expression {
                Expression::ConditionalExpression {
                    condition,
                    consequent,
                    alternate,
                } => {
                    let consequent_tag_value = self
                        .get_value_to_check_for_tag(
                            tag,
                            checking_presence,
                            Path::new_computed(consequent.clone()),
                            source_rustc_type,
                        )
                        .1;
                    let alternate_tag_value = self
                        .get_value_to_check_for_tag(
                            tag,
                            checking_presence,
                            Path::new_computed(alternate.clone()),
                            source_rustc_type,
                        )
                        .1;
                    return (
                        source_path.clone(),
                        condition.conditional_expression(consequent_tag_value, alternate_tag_value),
                    );
                }
                Expression::Join { left, right } => {
                    let left_tag_value = self
                        .get_value_to_check_for_tag(
                            tag,
                            checking_presence,
                            Path::new_computed(left.clone()),
                            source_rustc_type,
                        )
                        .1;
                    let right_tag_value = self
                        .get_value_to_check_for_tag(
                            tag,
                            checking_presence,
                            Path::new_computed(right.clone()),
                            source_rustc_type,
                        )
                        .1;
                    return (source_path.clone(), left_tag_value.join(right_tag_value));
                }
                Expression::WidenedJoin { operand, path } => {
                    let operand_tag_value = self
                        .get_value_to_check_for_tag(
                            tag,
                            checking_presence,
                            Path::new_computed(operand.clone()),
                            source_rustc_type,
                        )
                        .1;
                    let tag_path = Path::new_tag_field(path.clone());
                    return (tag_path.clone(), operand_tag_value.widen(&tag_path));
                }
                _ => {}
            }
        }

        // If the value located at source_path has sub-components, extract its tag field.
        // Otherwise, the source value is a scalar, i.e., tags are associated with it directly,
        // so we use the value itself as the tag field value.
        if !source_rustc_type.is_scalar() {
            self.block_visitor
                .bv
                .extract_tag_field_of_non_scalar_value_at(&source_path, source_rustc_type)
        } else {
            (
                source_path.clone(),
                self.block_visitor
                    .bv
                    .lookup_path_and_refine_result(source_path, source_rustc_type),
            )
        }
    }

    /// Update the state so that the call result is the value of the model field (or the default
    /// value if there is no field).
    #[logfn_inputs(TRACE)]
    fn handle_get_model_field(&mut self) {
        let target_type = self
            .type_visitor()
            .get_rustc_place_type(&self.destination, self.block_visitor.bv.current_span);
        checked_assume!(self.actual_args.len() == 3);

        // The current value, if any, of the model field are a set of (path, value) pairs
        // where each path is rooted by qualifier.model_field(..)
        let mut qualifier = self.actual_args[0].0.clone();
        if matches!(&self.actual_argument_types[0].kind(), TyKind::Ref { .. }) {
            let target_type = ExpressionType::from(
                self.type_visitor()
                    .get_dereferenced_type(self.actual_argument_types[0])
                    .kind(),
            );
            qualifier = Path::new_deref(qualifier, target_type);
        }
        let field_name = self.coerce_to_string(&self.actual_args[1].0.clone());
        let source_path = Path::new_model_field(qualifier, field_name)
            .canonicalize(&self.block_visitor.bv.current_environment);

        let target_path = self.block_visitor.visit_rh_place(&self.destination);
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
                    self.block_visitor.bv.update_value_at(target_path, rval);
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
        if let Some(target) = &self.target {
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
        if let Some(target) = &self.target {
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
            let message = self.coerce_to_string(&self.actual_args[1].0.clone());
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

        let mut qualifier = self.actual_args[0].0.clone();
        if matches!(&self.actual_argument_types[0].kind(), TyKind::Ref { .. }) {
            let target_type = ExpressionType::from(
                self.type_visitor()
                    .get_dereferenced_type(self.actual_argument_types[0])
                    .kind(),
            );
            qualifier = Path::new_deref(qualifier, target_type);
        }
        let field_name = self.coerce_to_string(&self.actual_args[1].0.clone());
        let target_path = Path::new_model_field(qualifier, field_name)
            .canonicalize(&self.block_visitor.bv.current_environment);
        let source_path = self.actual_args[2].0.clone();
        let target_type = self.actual_argument_types[2];
        self.block_visitor
            .bv
            .copy_or_move_elements(target_path, source_path, target_type, true);
        if let Some(target) = &self.target {
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
            .canonicalize(&self.block_visitor.bv.current_environment);
        self.block_visitor.bv.update_value_at(layout_path, layout);

        // Signal to the caller that there is no return result
        abstract_value::BOTTOM.into()
    }

    /// Copies a slice of elements from the source to the destination.
    #[logfn_inputs(TRACE)]
    fn handle_copy_non_overlapping(&mut self) {
        checked_assume!(self.actual_args.len() == 3);
        let source_path =
            Path::new_deref(self.actual_args[0].0.clone(), ExpressionType::NonPrimitive)
                .canonicalize(&self.environment_before_call);
        let target_root =
            Path::new_deref(self.actual_args[1].0.clone(), ExpressionType::NonPrimitive)
                .canonicalize(&self.environment_before_call);
        let count = self.actual_args[2].1.clone();
        let target_path = Path::new_slice(target_root, count);
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
        let target_type = ExpressionType::from(
            self.type_visitor()
                .get_dereferenced_type(self.actual_argument_types[0])
                .kind(),
        );
        let discriminant_path =
            Path::new_discriminant(Path::new_deref(self.actual_args[0].0.clone(), target_type))
                .canonicalize(&self.block_visitor.bv.current_environment);
        let mut discriminant_value = self
            .block_visitor
            .bv
            .lookup_path_and_refine_result(discriminant_path, self.block_visitor.bv.tcx.types.u128);
        // If `T` has no discriminant, return 0.
        match self.callee_generic_arguments {
            None => assume_unreachable!(
                "expected discriminant_value function call to have a generic argument"
            ),
            Some(rustc_gen_args) => {
                checked_assume!(rustc_gen_args.len() == 1);
                match rustc_gen_args[0].unpack() {
                    GenericArgKind::Type(ty) => match ty.kind() {
                        TyKind::Adt(def, _) if def.is_enum() => {}
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
        let target_path = self.block_visitor.visit_rh_place(&self.destination);
        self.block_visitor
            .bv
            .update_value_at(target_path, discriminant_value);
        self.use_entry_condition_as_exit_condition();
    }

    /// Swaps a slice of elements from the source to the destination.
    #[logfn_inputs(TRACE)]
    fn handle_swap_non_overlapping(&mut self) {
        checked_assume!(self.actual_args.len() == 3);
        let ty = self.actual_argument_types[0];
        let target_root =
            Path::new_deref(self.actual_args[0].0.clone(), ExpressionType::NonPrimitive);
        let source_root =
            Path::new_deref(self.actual_args[1].0.clone(), ExpressionType::NonPrimitive);
        let count = self.actual_args[2].1.clone();
        let source_slice = Path::new_slice(source_root.clone(), count.clone());
        let target_slice = Path::new_slice(target_root.clone(), count.clone());
        let temp_root = Path::new_local(999_999, 0);
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
        let ty = self
            .type_visitor()
            .get_rustc_place_type(&self.destination, self.block_visitor.bv.current_span);
        let (_, heap_path) = self
            .block_visitor
            .bv
            .get_new_heap_block(length, alignment, false, ty);
        AbstractValue::make_reference(heap_path)
    }

    /// Returns a new heap memory block with the given byte length and with the zeroed flag set.
    #[logfn_inputs(TRACE)]
    fn handle_rust_alloc_zeroed(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_args.len() == 2);
        let length = self.actual_args[0].1.clone();
        let alignment = self.actual_args[1].1.clone();
        let ty = self
            .type_visitor()
            .get_rustc_place_type(&self.destination, self.block_visitor.bv.current_span);
        let (_, heap_path) = self
            .block_visitor
            .bv
            .get_new_heap_block(length, alignment, true, ty);
        AbstractValue::make_reference(heap_path)
    }

    /// Sets the length of the heap block to a new value and removes index paths as necessary
    /// if the new length is known and less than the old lengths.
    #[logfn_inputs(TRACE)]
    fn handle_rust_realloc(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_args.len() == 4);
        // Get path to the heap block to reallocate
        let target_type = ExpressionType::from(
            self.type_visitor()
                .get_dereferenced_type(self.actual_argument_types[0])
                .kind(),
        );
        let heap_block_path = Path::new_deref(self.actual_args[0].0.clone(), target_type);

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
            .canonicalize(&self.block_visitor.bv.current_environment);
        self.block_visitor
            .bv
            .update_value_at(layout_path.clone(), new_length_layout);
        let layout_path2 = Path::new_layout(layout_path);
        self.block_visitor
            .bv
            .update_value_at(layout_path2, layout_param);

        // Return the original heap block reference as the result
        self.actual_args[0].1.clone()
    }

    /// Set the call result to an offset derived from the arguments. Does no checking.
    #[logfn_inputs(TRACE)]
    fn handle_arith_offset(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_args.len() == 2);
        let base_val = self.actual_args[0].1.clone();
        let offset_val = self.actual_args[1].1.clone();
        let offset_scale = self.handle_size_of().cast(ExpressionType::Isize);
        let offset_in_bytes = offset_val.multiply(offset_scale);
        base_val.offset(offset_in_bytes)
    }

    /// Update the state to reflect a call to an intrinsic binary operation that returns a tuple
    /// of an operation result, modulo its max value, and a flag that indicates if the max value
    /// was exceeded.
    #[logfn_inputs(TRACE)]
    fn handle_checked_binary_operation(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_args.len() == 2);
        let bin_op = match self.callee_known_name {
            KnownNames::StdIntrinsicsMulWithOverflow => mir::BinOp::Mul,
            _ => assume_unreachable!(),
        };
        let target_path = self.block_visitor.visit_rh_place(&self.destination);
        let path0 = Path::new_field(target_path.clone(), 0);
        let path1 = Path::new_field(target_path.clone(), 1);
        let target_type = self
            .type_visitor()
            .get_target_path_type(&path0, self.block_visitor.bv.current_span);
        let left = self.actual_args[0].1.clone();
        let right = self.actual_args[1].1.clone();
        let modulo = target_type.modulo_value();
        let (result, overflow_flag) =
            BlockVisitor::do_checked_binary_op(bin_op, target_type, left, right);
        let (modulo_result, overflow_flag) = if !modulo.is_bottom() {
            (result.remainder(target_type.modulo_value()), overflow_flag)
        } else {
            // todo: figure out an expression that represents the truncated overflow of a
            // signed operation.
            let unknown_typed_value = AbstractValue::make_typed_unknown(target_type, path0.clone());
            (
                overflow_flag.conditional_expression(unknown_typed_value, result),
                overflow_flag,
            )
        };
        self.block_visitor.bv.update_value_at(path0, modulo_result);
        self.block_visitor.bv.update_value_at(path1, overflow_flag);
        AbstractValue::make_typed_unknown(target_type, target_path)
    }

    /// If `ty.needs_drop(...)` returns `true`, then `ty` is definitely
    /// non-copy and *might* have a destructor attached; if it returns
    /// `false`, then `ty` definitely has no destructor (i.e., no drop glue).
    #[logfn_inputs(TRACE)]
    fn handle_needs_drop(&mut self) -> Rc<AbstractValue> {
        let sym = rustc_span::Symbol::intern("T");
        let t = (self.callee_generic_argument_map.as_ref())
            .expect("std::intrinsics::needs_drop must be called with generic arguments")
            .get(&sym)
            .expect("std::intrinsics::needs_drop must have generic argument T")
            .expect_ty();
        let param_env = self.block_visitor.bv.tcx.param_env(self.callee_def_id);
        let result = t.needs_drop(self.block_visitor.bv.tcx, param_env);
        Rc::new(result.into())
    }

    /// Set the call result to an offset derived from the arguments.
    /// Checks that the resulting offset is either in bounds or one
    /// byte past the end of an allocated object.
    #[logfn_inputs(TRACE)]
    fn handle_offset(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_args.len() == 2);
        let base_val = self.actual_args[0].1.clone();
        let offset_val = self.actual_args[1].1.clone();
        let offset_scale = self.handle_size_of().cast(ExpressionType::Isize);
        let offset_in_bytes = offset_val.multiply(offset_scale);
        let result = base_val.offset(offset_in_bytes);
        if self.block_visitor.bv.check_for_errors
            && self.block_visitor.bv.function_being_analyzed_is_root()
        {
            self.block_visitor.bv.check_offset(&result)
        }
        //todo: if the function is not root, promote this to a precondition
        result
    }

    /// Moves `source` into the referenced `dest`, returning the previous `dest` value.
    #[logfn_inputs(TRACE)]
    fn handle_mem_replace(&mut self) {
        checked_assume!(self.actual_args.len() == 2);
        let target_type = ExpressionType::from(
            self.type_visitor()
                .get_dereferenced_type(self.actual_argument_types[0])
                .kind(),
        );
        let dest_path = Path::new_deref(self.actual_args[0].0.clone(), target_type)
            .canonicalize(&self.block_visitor.bv.current_environment);
        let source_path = &self.actual_args[1].0;
        let target_path = self.block_visitor.visit_rh_place(&self.destination);
        let root_rustc_type = self
            .type_visitor()
            .get_rustc_place_type(&self.destination, self.block_visitor.bv.current_span);
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
        self.use_entry_condition_as_exit_condition();
    }

    /// Gets the size in bytes of the type parameter T of the std::mem::size_of<T> function.
    /// Returns an unknown value of type u128 if T is not a concrete type.
    #[logfn_inputs(TRACE)]
    fn handle_size_of(&mut self) -> Rc<AbstractValue> {
        let sym = rustc_span::Symbol::intern("T");
        let t = (self.callee_generic_argument_map.as_ref())
            .expect("std::intrinsics::size_of must be called with generic arguments")
            .get(&sym)
            .expect("std::intrinsics::size_of must have generic argument T")
            .expect_ty();
        if let Ok(ty_and_layout) = self.type_visitor().layout_of(t) {
            if !ty_and_layout.is_unsized() {
                return Rc::new((ty_and_layout.layout.size().bytes() as u128).into());
            }
        }
        let path = self.block_visitor.visit_rh_place(&self.destination);
        AbstractValue::make_typed_unknown(ExpressionType::U128, path)
    }

    /// Determines whether the raw bytes of the two values are equal.
    fn handle_raw_eq(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_args.len() == 2);
        let left_val = self.actual_args[0].1.clone();
        let right_val = self.actual_args[1].1.clone();
        let len_val = self.handle_size_of();
        let zero = Rc::new(ConstantDomain::U128(0).into());
        AbstractValue::make_memcmp(left_val, right_val, len_val).equals(zero)
    }

    /// Calls implementation provided memcmp.
    ///
    /// Interprets the data as u8.
    ///
    /// Returns 0 for equal, < 0 for less than and > 0 for greater than.
    fn handle_memcmp(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_args.len() == 3);
        let left_val = self.actual_args[0].1.clone();
        let right_val = self.actual_args[1].1.clone();
        let len_val = self.actual_args[2].1.clone();
        AbstractValue::make_memcmp(left_val, right_val, len_val)
    }

    /// Returns the [ABI]-required minimum alignment of the type of the value that `val` points to.
    ///
    /// Every reference to a value of the type `T` must be a multiple of this number.
    fn handle_min_align_of_val(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_argument_types.len() == 1);
        let t = self
            .type_visitor()
            .get_dereferenced_type(self.actual_argument_types[0]);
        if let Ok(ty_and_layout) = self.type_visitor().layout_of(t) {
            return Rc::new((ty_and_layout.layout.align().abi.bytes() as u128).into());
        }
        // todo: need an expression that resolves to the value size once the value is known (typically after call site refinement).
        let path = self.block_visitor.visit_rh_place(&self.destination);
        AbstractValue::make_typed_unknown(ExpressionType::U128, path)
    }

    /// Returns the size of the pointed-to value in bytes.
    ///
    /// This is usually the same as `size_of::<T>()`. However, when `T` *has* no
    /// statically-known size, e.g., a slice [`[T]`][slice] or a [trait object],
    /// then `size_of_val` can be used to get the dynamically-known size.
    #[logfn_inputs(TRACE)]
    fn handle_size_of_val(&mut self) -> Rc<AbstractValue> {
        checked_assume!(self.actual_argument_types.len() == 1);
        let t = self.actual_argument_types[0];
        checked_assume!(self.actual_args.len() == 1);
        let val = &self.actual_args[0].1;
        if matches!(val.expression, Expression::HeapBlock { .. }) {
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
        } else if self.type_visitor().is_slice_pointer(t.kind()) {
            let elem_t = self.type_visitor().get_element_type(t);
            if let Ok(ty_and_layout) = self.type_visitor().layout_of(elem_t) {
                if !ty_and_layout.is_unsized() {
                    let elem_size_val: Rc<AbstractValue> =
                        Rc::new((ty_and_layout.layout.size().bytes() as u128).into());
                    let length_path = Path::new_length(self.actual_args[0].0.clone());
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
        if let Ok(ty_and_layout) = self.type_visitor().layout_of(t) {
            if !ty_and_layout.is_unsized() {
                return Rc::new((ty_and_layout.layout.size().bytes() as u128).into());
            }
        }
        // todo: need an expression that resolves to the value size once the value is known (typically after call site refinement).
        let path = self.block_visitor.visit_rh_place(&self.destination);
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
        let source_path = self.actual_args[0].0.clone();
        let source_rustc_type = self
            .callee_generic_arguments
            .expect("rustc type error")
            .get(0)
            .expect("rustc type error")
            .expect_ty();
        let target_path = self.block_visitor.visit_rh_place(&self.destination);
        let target_rustc_type = self
            .type_visitor()
            .get_rustc_place_type(&self.destination, self.block_visitor.bv.current_span);
        self.block_visitor.bv.copy_and_transmute(
            source_path,
            source_rustc_type,
            target_path,
            target_rustc_type,
        );
        self.use_entry_condition_as_exit_condition();
    }

    #[logfn_inputs(TRACE)]
    fn handle_write_bytes(&mut self) {
        checked_assume!(self.actual_args.len() == 3);
        let target_type = ExpressionType::from(
            self.type_visitor()
                .get_dereferenced_type(self.actual_argument_types[0])
                .kind(),
        );
        let dest_path = Path::new_deref(self.actual_args[0].0.clone(), target_type)
            .canonicalize(&self.block_visitor.bv.current_environment);
        let dest_type = self.actual_argument_types[0];
        let source_path = self.actual_args[1]
            .0
            .canonicalize(&self.block_visitor.bv.current_environment);
        let byte_value = &self.actual_args[1].1;
        let count_value = self.actual_args[2].1.clone();
        let elem_type = self
            .callee_generic_arguments
            .expect("write_bytes<T>")
            .get(0)
            .expect("write_bytes<T>")
            .expect_ty();
        let mut elem_size = self.type_visitor().get_type_size(elem_type);
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
                .update_value_at(dest_pattern, source_value);
        } else if let Expression::CompileTimeConstant(ConstantDomain::U128(count)) =
            &count_value.expression
        {
            if let TyKind::Adt(..) | TyKind::Tuple(..) = &elem_type.kind() {
                for i in 0..(*count as usize) {
                    let dest_field = Path::new_field(dest_path.clone(), i);
                    let field_type = self
                        .type_visitor()
                        .get_path_rustc_type(&dest_field, self.block_visitor.bv.current_span);
                    let field_size = self.type_visitor().get_type_size(field_type);
                    elem_size -= field_size;
                    let field_value = repeated_bytes(field_size, byte_value);
                    self.block_visitor
                        .bv
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

    /// Give diagnostic depending on self.bv.options.diag_level
    #[logfn_inputs(TRACE)]
    pub fn report_incomplete_summary(&mut self) {
        if self.block_visitor.might_be_reachable().unwrap_or(true) {
            if let Some(promotable_entry_condition) = self
                .block_visitor
                .bv
                .current_environment
                .entry_condition
                .extract_promotable_conjuncts(false)
            {
                if promotable_entry_condition.as_bool_if_known().is_none()
                    && self.block_visitor.bv.cv.options.diag_level != DiagLevel::Default
                {
                    let precondition = Precondition {
                        condition: promotable_entry_condition.logical_not(),
                        message: Rc::from("incomplete analysis of call because of failure to resolve a nested call"),
                        provenance: None,
                        spans: vec![self.block_visitor.bv.current_span.source_callsite()],
                    };
                    self.block_visitor.bv.preconditions.push(precondition);
                }
                return;
            }
            // Don't stop the analysis if we are building a call graph.
            self.block_visitor.bv.analysis_is_incomplete =
                self.block_visitor.bv.cv.options.call_graph_config.is_none();
            // If the callee is local, there will already be a diagnostic about the incomplete summary.
            if !self.callee_def_id.is_local()
                && self.block_visitor.bv.cv.options.diag_level != DiagLevel::Default
            {
                let warning = self.block_visitor.bv.cv.session.struct_span_warn(
                    self.block_visitor.bv.current_span,
                    "the called function could not be completely analyzed",
                );
                self.block_visitor.bv.emit_diagnostic(warning);
            }
            let argument_type_hint = if let Some(func) = &self.callee_func_ref {
                format!(" (foreign fn argument key: {})", func.argument_type_key)
            } else {
                "".to_string()
            };
            // todo: when a call site has an expression that does not result in a compile time
            // constant function, perhaps construct a dummy function that is the join of the
            // summaries of the function constants that might flow into the expression.
            //todo: handle parameters that are arrays of functions
            if self.block_visitor.bv.def_id.is_local() && !self.callee_def_id.is_local() {
                info!(
                    "function {} can't be reliably analyzed because it calls function {} which could not be summarized{}.",
                    utils::summary_key_str(self.block_visitor.bv.tcx, self.block_visitor.bv.def_id),
                    utils::summary_key_str(self.block_visitor.bv.tcx, self.callee_def_id),
                    argument_type_hint,
                );
            } else {
                debug!(
                    "function {} can't be reliably analyzed because it calls function {} which could not be summarized{}.",
                    utils::summary_key_str(self.block_visitor.bv.tcx, self.block_visitor.bv.def_id),
                    utils::summary_key_str(self.block_visitor.bv.tcx, self.callee_def_id),
                    argument_type_hint,
                );
            }
            debug!("def_id {:?}", self.callee_def_id);
        }
    }

    /// Refines the summary using the call arguments and local environment and transfers
    /// the side effects of the summary into the current environment, while also checking
    /// preconditions and add the post conditions to the exit condition guarding the post call target block.
    #[logfn_inputs(TRACE)]
    pub fn transfer_and_refine_into_current_environment(&mut self, function_summary: &Summary) {
        debug!("def_id {:?}", self.callee_def_id);
        debug!("summary {:?}", function_summary);
        debug!("pre env {:?}", self.block_visitor.bv.current_environment);
        debug!(
            "target {:?} arguments {:?}",
            self.destination, self.actual_args
        );
        self.check_preconditions_if_necessary(function_summary);
        check_for_early_return!(self.block_visitor.bv);
        self.transfer_and_refine_normal_return_state(function_summary);
        check_for_early_return!(self.block_visitor.bv);
        self.add_post_condition_to_exit_conditions(function_summary);
        debug!("post env {:?}", self.block_visitor.bv.current_environment);
    }

    /// If we are checking for errors and have not assumed the preconditions of the called function
    /// and we are not in angelic mode and have not already reported an error for this call,
    /// then check the preconditions and report any conditions that are not known to hold at this point.
    #[logfn_inputs(TRACE)]
    pub fn check_preconditions_if_necessary(&mut self, function_summary: &Summary) {
        if self.block_visitor.bv.check_for_errors
            && self
                .block_visitor
                .bv
                .current_environment
                .entry_condition
                .as_bool_if_known()
                .unwrap_or(true)
            && !self.block_visitor.bv.assume_preconditions_of_next_call
            && !self
                .block_visitor
                .bv
                .already_reported_errors_for_call_to
                .contains(&self.callee_fun_val)
        {
            self.check_function_preconditions(function_summary);
        } else {
            if let Some(fr) = &self.callee_func_ref {
                if fr.summary_cache_key.ends_with(".deref") {
                    return;
                }
            }
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
        // A precondition can refer to the result if the precondition prevents the result expression
        // from overflowing.
        let result = Some(self.block_visitor.visit_rh_place(&self.destination));
        for precondition in &function_summary.preconditions {
            let mut refined_condition = precondition.condition.refine_parameters_and_paths(
                &self.actual_args,
                &result,
                &self.environment_before_call,
                &self.block_visitor.bv.current_environment,
                self.block_visitor.bv.fresh_variable_offset,
            );
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

            if !entry_cond_as_bool.unwrap_or(true) {
                // The call is unreachable, so the precondition does not matter
                continue;
            }

            if refined_condition.is_bottom() {
                // The precondition has no value, assume it is unreachable after all.
                debug!("precondition refines to BOTTOM {:?}", precondition);
                continue;
            }

            let warn;
            if !refined_precondition_as_bool.unwrap_or(true) {
                // The precondition is definitely false.
                if !entry_cond_as_bool.unwrap_or(true) {
                    // The call is unreachable, so the precondition does not matter
                    continue;
                }
                if self.block_visitor.bv.function_being_analyzed_is_root() {
                    // This diagnostic says that the precondition is false and since
                    // we know for certain that it will be false, should this call be reached,
                    // it seems appropriate to issue an error message rather than a warning.
                    self.issue_diagnostic_for_call(precondition, &refined_condition, false);
                    return;
                } else {
                    // Promote the precondition, but be assertive.
                    // When the caller fails to meet the precondition, failure is certain.
                    warn = false;
                }
            } else {
                warn = true;
            }

            // Is the precondition a tag check for a tag that flows from a subcomponent to the
            // container?
            if let Expression::UnknownTagCheck {
                operand,
                tag,
                checking_presence,
            } = &refined_condition.expression
            {
                if tag.is_propagated_by(TagPropagation::SuperComponent) {
                    // Look at sub components. If components that are located via
                    // pointers are tagged, those tags will not have propagated to here
                    // because the pointers are unidirectional.
                    if *checking_presence
                        && operand.expression.has_tagged_subcomponent(
                            tag,
                            &self.block_visitor.bv.current_environment,
                        )
                    {
                        continue;
                    }
                }
            }

            // If the current function is not an analysis root, promote the precondition, subject to a k-limit.
            if (!self.block_visitor.bv.function_being_analyzed_is_root()
                || self.block_visitor.bv.cv.options.diag_level == DiagLevel::Default)
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
                let promoted_condition = match (
                    self.block_visitor
                        .bv
                        .current_environment
                        .entry_condition
                        .extract_promotable_conjuncts(false),
                    refined_condition.extract_promotable_disjuncts(false),
                ) {
                    (Some(promotable_entry_condition), Some(promotable_condition)) => {
                        promotable_entry_condition
                            .logical_not()
                            .or(promotable_condition)
                    }
                    (Some(promotable_entry_condition), None) => {
                        if self.block_visitor.bv.cv.options.diag_level == DiagLevel::Default {
                            // If refined condition cannot be promoted, it may not be reasonable
                            // to require our caller to prove that this call can't be reached.
                            // Hence, we'll just leave the precondition un-promoted.
                            continue;
                        } else {
                            promotable_entry_condition.logical_not()
                        }
                    }
                    (None, Some(promotable_condition)) => promotable_condition,
                    _ => Rc::new(abstract_value::FALSE),
                };
                if promoted_condition.as_bool_if_known().is_none() {
                    if self.block_visitor.bv.current_span.in_derive_expansion() {
                        info!("derive macro has warning: {:?}", precondition.message);
                        // do not propagate preconditions across derive macros since
                        // derived code is pretty much foreign code.
                        continue;
                    }

                    if (self.block_visitor.bv.treat_as_foreign
                        || !self.block_visitor.bv.def_id.is_local())
                        && !matches!(
                            self.block_visitor.bv.cv.options.diag_level,
                            DiagLevel::Paranoid
                        )
                        && precondition.message.contains("result unwrap failed")
                    {
                        // When foreign code unwraps a result, it is unlikely to be a parameter check.
                        // Instead, let's assume that the code intends a panic to happen if the
                        // result is not OK.
                        continue;
                    }

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
                    continue;
                } else if !refined_condition.as_bool_if_known().unwrap_or(true)
                    && !self.block_visitor.bv.function_being_analyzed_is_root()
                {
                    if let Some(true) = self
                        .block_visitor
                        .bv
                        .current_environment
                        .entry_condition
                        .as_bool_if_known()
                    {
                        // Just a pass through function
                        let mut promoted_precondition = precondition.clone();
                        promoted_precondition.condition = refined_condition;
                        self.block_visitor
                            .bv
                            .preconditions
                            .push(promoted_precondition);
                        continue;
                    }
                }
            }

            // The precondition cannot be promoted, so the buck stops here.
            if precondition
                .message
                .starts_with("incomplete analysis of call")
            {
                // If the precondition is not satisfied, the summary of the callee is incomplete
                // and so should be the summary of this method, but
                // if we are building a call graph we don't want the analysis to stop.
                self.block_visitor.bv.analysis_is_incomplete =
                    self.block_visitor.bv.cv.options.call_graph_config.is_none();
                if self.block_visitor.bv.cv.options.diag_level == DiagLevel::Default {
                    // Don't give a diagnostic in default mode, since it is hard for casual users
                    // to do something about missing/incomplete summaries.
                    continue;
                }
            }
            if self.block_visitor.bv.cv.options.diag_level == DiagLevel::Default
                && refined_condition.expression.contains_top()
            {
                // If the refined precondition contains TOP expressions, precision has
                // been lost and the message is more likely than not a false positive.
                continue;
            }
            self.issue_diagnostic_for_call(precondition, &refined_condition, warn);
        }
    }

    // Issue a diagnostic, but only if there isn't already a diagnostic for this
    // function call.
    #[logfn_inputs(TRACE)]
    fn issue_diagnostic_for_call(
        &mut self,
        precondition: &Precondition,
        condition: &Rc<AbstractValue>,
        warn: bool,
    ) {
        if self.block_visitor.bv.check_for_errors
            && !self
                .block_visitor
                .bv
                .already_reported_errors_for_call_to
                .contains(&self.callee_fun_val)
        {
            self.block_visitor
                .emit_diagnostic_for_precondition(precondition, condition, warn);
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
        // Assign function result to place
        let target_path = self.block_visitor.visit_rh_place(&self.destination);
        let result_path = &Some(target_path.clone());
        // If the summary has a concrete type for the return result, use that type rather
        // than the possibly abstract type of the target path.
        let result_type = self
            .type_visitor()
            .get_type_from_index(function_summary.return_type_index);
        if !result_type.is_never() {
            self.type_visitor_mut()
                .set_path_rustc_type(target_path.clone(), result_type);
        }
        let return_value_path = Path::new_result();

        let mut pre_environment = self.environment_before_call.clone();
        // Transfer side effects
        if function_summary.is_computed && !function_summary.is_incomplete {
            // Effects on the heap
            for (path, value) in function_summary.side_effects.iter() {
                if path.is_rooted_by_non_local_structure() {
                    let rvalue = value.clone().refine_parameters_and_paths(
                        &self.actual_args,
                        result_path,
                        &self.environment_before_call,
                        &self.block_visitor.bv.current_environment,
                        self.block_visitor.bv.fresh_variable_offset,
                    );
                    let rpath = path.refine_parameters_and_paths(
                        &self.actual_args,
                        result_path,
                        &self.environment_before_call,
                        &self.block_visitor.bv.current_environment,
                        self.block_visitor.bv.fresh_variable_offset,
                    );
                    if rvalue.expression.infer_type() == ExpressionType::NonPrimitive {
                        let source_path = Path::get_as_path(rvalue.clone());
                        let source_type = self
                            .block_visitor
                            .bv
                            .type_visitor()
                            .get_path_rustc_type(&source_path, self.block_visitor.bv.current_span);
                        self.block_visitor.bv.copy_or_move_elements(
                            rpath.clone(),
                            source_path,
                            source_type,
                            false,
                        );
                    } else {
                        self.block_visitor
                            .bv
                            .update_value_at(rpath.clone(), rvalue.clone());
                    }
                    pre_environment.strong_update_value_at(rpath, rvalue);
                }
                check_for_early_return!(self.block_visitor.bv);
            }

            // Effects on the call result
            self.block_visitor.bv.transfer_and_refine(
                &function_summary.side_effects,
                target_path,
                &return_value_path,
                result_path,
                &self.actual_args,
                &pre_environment,
            );

            // Effects on the call arguments
            for (i, (target_path, _)) in self.actual_args.iter().enumerate() {
                let parameter_path = Path::new_parameter(i + 1);
                self.block_visitor.bv.transfer_and_refine(
                    &function_summary.side_effects,
                    target_path.clone(),
                    &parameter_path,
                    result_path,
                    &self.actual_args,
                    &pre_environment,
                );
                check_for_early_return!(self.block_visitor.bv);
            }
        } else {
            // We don't know anything other than the return value type.
            // We'll assume there were no side effects and no preconditions.
            let args = self.actual_args.iter().map(|(_, a)| a.clone()).collect();
            let result_type = self
                .type_visitor()
                .get_place_type(&self.destination, self.block_visitor.bv.current_span);
            let result =
                self.callee_fun_val
                    .uninterpreted_call(args, result_type, return_value_path);
            self.block_visitor.bv.update_value_at(target_path, result);
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
        if let Some(target) = &self.target {
            let target_path = self.block_visitor.visit_lh_place(&self.destination);
            let result_path = &Some(target_path);
            let mut exit_condition = self
                .block_visitor
                .bv
                .current_environment
                .entry_condition
                .clone();
            if exit_condition.as_bool_if_known().unwrap_or(true) {
                if let Some(post_condition) = &function_summary.post_condition {
                    let refined_post_condition = post_condition.refine_parameters_and_paths(
                        &self.actual_args,
                        result_path,
                        &self.environment_before_call,
                        &self.block_visitor.bv.current_environment,
                        self.block_visitor.bv.fresh_variable_offset,
                    );
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

    /// Extracts the string from an AbstractDomain that is required to be a reference to a string literal.
    /// This is the case for helper MIRAI helper functions that are hidden in the documentation
    /// and that are required to be invoked via macros that ensure that the argument providing
    /// this value is always a string literal.
    #[logfn_inputs(TRACE)]
    fn coerce_to_string(&mut self, path: &Rc<Path>) -> Rc<str> {
        if let PathEnum::Computed { value } = &path.value {
            if let Expression::Reference(path) = &value.expression {
                if let PathEnum::Computed { value } = &path.value {
                    if let Expression::CompileTimeConstant(ConstantDomain::Str(s)) =
                        &value.expression
                    {
                        return s.clone();
                    }
                }
            }
        } else if let Some(value) = self.block_visitor.bv.current_environment.value_at(path) {
            if let Expression::Reference(path) = &value.expression {
                if let PathEnum::Computed { value } = &path.value {
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
                let tag_rustc_type = match rustc_gen_args[1].unpack() {
                    GenericArgKind::Type(rustc_type) => rustc_type,
                    _ => {
                        // The rust type checker should ensure that the second generic argument is a type.
                        assume_unreachable!(
                            "expected the second generic argument of tag-related function calls to be a type"
                        );
                    }
                };

                // The tag type should be a generic ADT whose first parameter is a constant.
                let tag_adt_def;
                let tag_substs_ref = match tag_rustc_type.kind() {
                    TyKind::Adt(adt_def, substs_ref) if substs_ref.len() > 0 => {
                        tag_adt_def = adt_def;
                        substs_ref
                    }
                    _ => {
                        if self.block_visitor.bv.check_for_errors {
                            let warning = self.block_visitor.bv.cv.session.struct_span_warn(
                                self.block_visitor.bv.current_span,
                                "the tag type should be a generic type whose first parameter is a constant of type TagPropagationSet",
                            );
                            self.block_visitor.bv.emit_diagnostic(warning);
                        }
                        return None;
                    }
                };

                // Extract the tag type's first parameter.
                let tag_propagation_set_rustc_const = match tag_substs_ref[0].unpack() {
                    GenericArgKind::Const(rustc_const)
                        if *rustc_const.ty().kind() == TyKind::Uint(UintTy::U128) =>
                    {
                        rustc_const
                    }
                    _ => {
                        if self.block_visitor.bv.check_for_errors {
                            let warning = self.block_visitor.bv.cv.session.struct_span_warn(
                                self.block_visitor.bv.current_span,
                                "the first parameter of the tag type should have type TagPropagationSet",
                            );
                            self.block_visitor.bv.emit_diagnostic(warning);
                        }
                        return None;
                    }
                };

                // Analyze the tag type's first parameter to obtain a compile-time constant.
                let tag_propagation_set_value = self
                    .block_visitor
                    .visit_const(&tag_propagation_set_rustc_const);
                if let Expression::CompileTimeConstant(ConstantDomain::U128(data)) =
                    &tag_propagation_set_value.expression
                {
                    let tag = Tag {
                        def_id: tag_adt_def.did().into(),
                        prop_set: *data,
                    };

                    // Record the tag if it is the constant-time verification tag.
                    self.check_and_record_constant_time_verification_tag(tag_adt_def.did(), &tag);

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
