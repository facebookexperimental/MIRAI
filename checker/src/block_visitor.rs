// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::abstract_value;
use crate::abstract_value::AbstractValue;
use crate::abstract_value::AbstractValueTrait;
use crate::body_visitor::BodyVisitor;
use crate::call_visitor::CallVisitor;
use crate::constant_domain::{ConstantDomain, FunctionReference};
use crate::environment::Environment;
use crate::expression::{Expression, ExpressionType};
use crate::k_limits;
use crate::known_names::KnownNames;
use crate::options::DiagLevel;
use crate::path::PathRefinement;
use crate::path::{Path, PathEnum, PathSelector};
use crate::smt_solver::{SmtResult, SmtSolver};
use crate::summaries::{Precondition, Summary};
use crate::tag_domain::Tag;
use crate::utils;

use crate::type_visitor::TypeVisitor;
use log_derive::*;
use mirai_annotations::*;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::mir::interpret::{alloc_range, ConstValue, GlobalAlloc, Scalar};
use rustc_middle::ty::adjustment::PointerCast;
use rustc_middle::ty::layout::PrimitiveExt;
use rustc_middle::ty::subst::{GenericArg, SubstsRef};
use rustc_middle::ty::{
    Const, ConstKind, FloatTy, IntTy, ParamConst, ScalarInt, Ty, TyKind, UintTy, Unevaluated,
};
use rustc_target::abi::{TagEncoding, VariantIdx, Variants};
use std::borrow::Borrow;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt::{Debug, Formatter, Result};
use std::rc::Rc;

/// Holds the state for the basic block visitor
pub struct BlockVisitor<'block, 'analysis, 'compilation, 'tcx> {
    pub bv: &'block mut BodyVisitor<'analysis, 'compilation, 'tcx>,
}

impl<'block, 'analysis, 'compilation, 'tcx> Debug
    for BlockVisitor<'block, 'analysis, 'compilation, 'tcx>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "BlockVisitor".fmt(f)
    }
}

impl<'block, 'analysis, 'compilation, 'tcx> BlockVisitor<'block, 'analysis, 'compilation, 'tcx> {
    pub fn new(
        body_visitor: &'block mut BodyVisitor<'analysis, 'compilation, 'tcx>,
    ) -> BlockVisitor<'block, 'analysis, 'compilation, 'tcx> {
        BlockVisitor { bv: body_visitor }
    }

    pub fn type_visitor(&self) -> &TypeVisitor<'tcx> {
        self.bv.type_visitor()
    }

    pub fn type_visitor_mut(&mut self) -> &mut TypeVisitor<'tcx> {
        self.bv.type_visitor_mut()
    }

    /// Visits each statement in order and then visits the terminator.
    #[logfn_inputs(TRACE)]
    pub fn visit_basic_block(
        &mut self,
        bb: mir::BasicBlock,
        terminator_state: &mut HashMap<mir::BasicBlock, Environment>,
    ) {
        let mir::BasicBlockData {
            ref statements,
            ref terminator,
            ..
        } = &self.bv.mir[bb];
        let mut location = bb.start_location();
        let terminator_index = statements.len();

        if !self.bv.check_for_errors {
            while location.statement_index < terminator_index {
                self.visit_statement(location, &statements[location.statement_index]);
                check_for_early_return!(self.bv);
                location.statement_index += 1;
            }
            terminator_state.insert(bb, self.bv.current_environment.clone());
        } else {
            check_for_early_return!(self.bv);
            location.statement_index = terminator_index;
        }

        if let Some(mir::Terminator {
            ref source_info,
            ref kind,
        }) = *terminator
        {
            self.visit_terminator(location, kind, *source_info);
        }
    }

    /// Calls a specialized visitor for each kind of statement.
    #[logfn_inputs(DEBUG)]
    fn visit_statement(&mut self, location: mir::Location, statement: &mir::Statement<'tcx>) {
        debug!("env {:?}", self.bv.current_environment);
        self.bv.current_location = location;
        let mir::Statement { kind, source_info } = statement;
        self.bv.current_span = source_info.span;
        match kind {
            mir::StatementKind::Assign(box (place, rvalue)) => {
                self.visit_assign(place, rvalue.borrow())
            }
            mir::StatementKind::FakeRead(..) => assume_unreachable!(),
            mir::StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => self.visit_set_discriminant(place, *variant_index),
            mir::StatementKind::StorageLive(local) => self.visit_storage_live(*local),
            mir::StatementKind::StorageDead(local) => self.visit_storage_dead(*local),
            mir::StatementKind::LlvmInlineAsm(inline_asm) => self.visit_llvm_inline_asm(inline_asm),
            mir::StatementKind::Retag(retag_kind, place) => self.visit_retag(*retag_kind, place),
            mir::StatementKind::AscribeUserType(..) => assume_unreachable!(),
            mir::StatementKind::Coverage(..) => (),
            mir::StatementKind::CopyNonOverlapping(box ref copy_info) => {
                self.visit_copy_non_overlapping(copy_info)
            }
            mir::StatementKind::Nop => (),
        }
    }

    /// Write the RHS Rvalue to the LHS Place.
    #[logfn_inputs(TRACE)]
    fn visit_assign(&mut self, place: &mir::Place<'tcx>, rvalue: &mir::Rvalue<'tcx>) {
        let mut path = self.visit_lh_place(place);
        match &path.value {
            PathEnum::PhantomData => {
                // No need to track this data
                return;
            }
            PathEnum::Computed { .. }
            | PathEnum::Offset { .. }
            | PathEnum::QualifiedPath { .. } => {
                path = path.canonicalize(&self.bv.current_environment);
            }
            _ => {}
        }
        self.visit_rvalue(path, rvalue);
    }

    /// Denotes a call to the intrinsic function copy_overlapping, where `src` and `dst` denotes the
    /// memory being read from and written to and size indicates how many bytes are being copied over.
    #[logfn_inputs(TRACE)]
    fn visit_copy_non_overlapping(&mut self, copy_info: &mir::CopyNonOverlapping<'tcx>) {
        let source_val = self.visit_operand(&copy_info.src);
        let source_path =
            Path::new_deref(Path::get_as_path(source_val), ExpressionType::NonPrimitive);
        let target_val = self.visit_operand(&copy_info.dst);
        let target_root =
            Path::new_deref(Path::get_as_path(target_val), ExpressionType::NonPrimitive);
        let count = self.visit_operand(&copy_info.count);
        let target_path = Path::new_slice(target_root, count);
        let collection_type = self.get_operand_rustc_type(&copy_info.dst);
        self.bv
            .copy_or_move_elements(target_path, source_path, collection_type, false);
    }

    /// Write the discriminant for a variant to the enum Place.
    #[logfn_inputs(TRACE)]
    fn visit_set_discriminant(
        &mut self,
        place: &mir::Place<'tcx>,
        variant_index: rustc_target::abi::VariantIdx,
    ) {
        let target_path = Path::new_discriminant(self.visit_rh_place(place));
        let ty = self
            .type_visitor()
            .get_rustc_place_type(place, self.bv.current_span);
        match ty.kind() {
            TyKind::Adt(..) | TyKind::Generator(..) => {
                let discr_ty = ty.discriminant_ty(self.bv.tcx);
                let discr_bits = match ty.discriminant_for_variant(self.bv.tcx, variant_index) {
                    Some(discr) => discr.val,
                    None => variant_index.as_u32() as u128,
                };
                let val = self.get_int_const_val(discr_bits, discr_ty);
                self.bv
                    .current_environment
                    .update_value_at(target_path, val);
            }
            _ => assume_unreachable!("rustc should ensure this"),
        }
    }

    /// Start a live range for the storage of the local.
    #[logfn_inputs(TRACE)]
    fn visit_storage_live(&mut self, local: mir::Local) {}

    /// End the current live range for the storage of the local.
    #[logfn_inputs(TRACE)]
    fn visit_storage_dead(&mut self, local: mir::Local) {
        let loc_ty = self.type_visitor().get_loc_ty(local);
        let type_index = self.type_visitor().get_index_for(loc_ty);
        let path = Path::new_local_parameter_or_result(
            local.as_usize(),
            self.bv.mir.arg_count,
            type_index,
        );
        self.bv
            .current_environment
            .update_value_at(path, abstract_value::BOTTOM.into());
    }

    /// Execute a piece of inline Assembly.
    #[logfn_inputs(TRACE)]
    fn visit_llvm_inline_asm(&mut self, inline_asm: &mir::LlvmInlineAsm<'tcx>) {
        let span = self.bv.current_span;
        let warning = self.bv.cv.session.struct_span_warn(
            span,
            "Inline llvm assembly code cannot be analyzed by MIRAI.",
        );
        self.bv.emit_diagnostic(warning);
        self.bv.analysis_is_incomplete = true;
    }

    /// Retag references in the given place, ensuring they got fresh tags.  This is
    /// part of the Stacked Borrows model. These statements are currently only interpreted
    /// by miri and only generated when "-Z mir-emit-retag" is passed.
    /// See <https://internals.rust-lang.org/t/stacked-borrows-an-aliasing-model-for-rust/8153/>
    /// for more details.
    #[logfn_inputs(TRACE)]
    fn visit_retag(&self, retag_kind: mir::RetagKind, place: &mir::Place<'tcx>) {
        // This seems to be an intermediate artifact of MIR generation and is related to aliasing.
        // We assume (and will attempt to enforce) that no aliasing of mutable pointers are present
        // in the programs we check.
        //
        // Therefore we simply ignore this.
    }

    /// Calls a specialized visitor for each kind of terminator.
    #[logfn_inputs(DEBUG)]
    fn visit_terminator(
        &mut self,
        location: mir::Location,
        kind: &mir::TerminatorKind<'tcx>,
        source_info: mir::SourceInfo,
    ) {
        debug!("env {:?}", self.bv.current_environment);
        self.bv.current_location = location;
        self.bv.current_span = source_info.span;
        match kind {
            mir::TerminatorKind::Goto { target } => self.visit_goto(*target),
            mir::TerminatorKind::SwitchInt {
                discr,
                switch_ty,
                targets,
            } => self.visit_switch_int(discr, switch_ty, targets),
            mir::TerminatorKind::Resume => self.visit_resume(),
            mir::TerminatorKind::Abort => self.visit_abort(),
            mir::TerminatorKind::Return => self.visit_return(),
            mir::TerminatorKind::Unreachable => self.visit_unreachable(),
            mir::TerminatorKind::Drop {
                place,
                target,
                unwind,
            } => self.visit_drop(place, *target, *unwind),
            mir::TerminatorKind::DropAndReplace { .. } => assume_unreachable!(),
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                cleanup,
                from_hir_call,
                fn_span,
            } => self.visit_call(func, args, destination, *cleanup, *from_hir_call, fn_span),
            mir::TerminatorKind::Assert {
                cond,
                expected,
                msg,
                target,
                cleanup,
            } => self.visit_assert(cond, *expected, msg, *target, *cleanup),
            mir::TerminatorKind::Yield { .. } => assume_unreachable!(),
            mir::TerminatorKind::GeneratorDrop => assume_unreachable!(),
            mir::TerminatorKind::FalseEdge { .. } => assume_unreachable!(),
            mir::TerminatorKind::FalseUnwind { .. } => assume_unreachable!(),
            mir::TerminatorKind::InlineAsm { destination, .. } => {
                self.visit_inline_asm(destination);
            }
        }
    }

    /// block should have one successor in the graph; we jump there
    #[logfn_inputs(TRACE)]
    fn visit_goto(&mut self, target: mir::BasicBlock) {
        // Propagate the entry condition to the successor block.
        self.bv
            .current_environment
            .exit_conditions
            .insert_mut(target, self.bv.current_environment.entry_condition.clone());
    }

    /// Operand evaluates to an integer; jump depending on its value
    /// to one of the targets, and otherwise fallback to `otherwise`.
    #[logfn_inputs(TRACE)]
    fn visit_switch_int(
        &mut self,
        discr: &mir::Operand<'tcx>,
        switch_ty: rustc_middle::ty::Ty<'tcx>,
        targets: &rustc_middle::mir::SwitchTargets,
    ) {
        let mut default_exit_condition = self.bv.current_environment.entry_condition.clone();
        let discr = self.visit_operand(discr);

        // Check if the discriminant is not attached with the tag for constant-time verification.
        if self.bv.check_for_errors {
            if let Some(tag_name) = &self.bv.cv.options.constant_time_tag_name {
                match self.bv.cv.constant_time_tag_cache {
                    None => {
                        // Check if the unknown-constant-time-tag diagnostic has been emitted.
                        if !self.bv.cv.constant_time_tag_not_found {
                            self.bv.cv.constant_time_tag_not_found = true;
                            let span = self.bv.current_span;
                            let warning = self.bv.cv.session.struct_span_warn(
                                span,
                                format!(
                                    "unknown tag type for constant-time verification: {}",
                                    tag_name
                                )
                                .as_str(),
                            );
                            self.bv.emit_diagnostic(warning);
                        }
                    }
                    Some(tag) => self.check_tag_existence_on_value(
                        &discr,
                        "branch condition",
                        tag,
                        tag_name,
                        false,
                    ),
                }
            }
        }

        // Continue to deal with the branch targets.
        let discr = discr.as_int_if_known().unwrap_or(discr);
        for (i, target) in targets.iter() {
            let val = self.get_int_const_val(i, switch_ty);
            let cond = discr.equals(val);
            let exit_condition = self
                .bv
                .current_environment
                .entry_condition
                .and(cond.clone());
            let not_cond = cond.logical_not();
            default_exit_condition = default_exit_condition.and(not_cond);
            let existing_exit_condition = self
                .bv
                .current_environment
                .exit_conditions
                .get(&target)
                .cloned();
            if let Some(existing_exit_condition) = existing_exit_condition {
                // There are multiple branches with the same target.
                // In this case, we use the disjunction of the branch conditions as the exit condition.
                self.bv
                    .current_environment
                    .exit_conditions
                    .insert_mut(target, existing_exit_condition.or(exit_condition));
            } else {
                self.bv
                    .current_environment
                    .exit_conditions
                    .insert_mut(target, exit_condition);
            }
        }
        self.bv
            .current_environment
            .exit_conditions
            .insert_mut(targets.otherwise(), default_exit_condition);
    }

    /// Indicates that the landing pad is finished and unwinding should
    /// continue. Emitted by build::scope::diverge_cleanup.
    #[logfn_inputs(TRACE)]
    fn visit_resume(&self) {}

    /// Indicates that the landing pad is finished and that the process
    /// should abort. Used to prevent unwinding for foreign items.
    #[logfn_inputs(TRACE)]
    fn visit_abort(&self) {}

    /// Indicates a normal return. The return place should have
    /// been filled in by now. This should occur at most once.
    #[logfn_inputs(TRACE)]
    fn visit_return(&mut self) {
        if self.bv.check_for_errors {
            // Done with fixed point, so prepare to summarize.
            if self.bv.post_condition.is_none() {
                if let Some(promotable_entry_condition) = self
                    .bv
                    .current_environment
                    .entry_condition
                    .extract_promotable_conjuncts(true)
                {
                    if promotable_entry_condition.as_bool_if_known().is_none() {
                        // If no post condition has been explicitly supplied and if the entry condition is interesting
                        // then make the entry condition a post condition, because the function only returns
                        // if this condition is true and thus the caller can assume the condition in its
                        // normal return path.
                        self.bv.post_condition = Some(promotable_entry_condition);
                    }
                }
            }
            // When the summary is prepared the current environment might be different, so remember this one.
            self.bv.exit_environment = Some(self.bv.current_environment.clone());
        }
    }

    /// Indicates a terminator that can never be reached.
    #[logfn_inputs(TRACE)]
    fn visit_unreachable(&mut self) {
        // An unreachable terminator is the compiler's way to tell us that this block will
        // actually never be reached because the type system says so.
        // Having the block in the control flow graph allows the join to remove the condition
        // guarding entry to this block.
    }

    /// Drop the Place
    #[logfn_inputs(TRACE)]
    fn visit_drop(
        &mut self,
        place: &mir::Place<'tcx>,
        target: mir::BasicBlock,
        unwind: Option<mir::BasicBlock>,
    ) {
        let place_path = self.get_path_for_place(place);
        let path = place_path.canonicalize(&self.bv.current_environment);
        let mut ty = self
            .type_visitor()
            .get_path_rustc_type(&path, self.bv.current_span);
        if ty.is_never() {
            ty = self
                .type_visitor()
                .get_rustc_place_type(place, self.bv.current_span);
            debug!("ty {:?}", ty);
        }
        ty = self.type_visitor().remove_transparent_wrappers(ty);
        self.type_visitor_mut()
            .set_path_rustc_type(path.clone(), ty);

        if let TyKind::Adt(def, substs) = ty.kind() {
            if let Some(destructor) = self.bv.tcx.adt_destructor(def.did) {
                let actual_argument_types = vec![self
                    .bv
                    .cv
                    .tcx
                    .mk_mut_ref(self.bv.cv.tcx.lifetimes.re_static, ty)];
                let callee_generic_arguments = self
                    .type_visitor()
                    .specialize_substs(substs, &self.type_visitor().generic_argument_map);
                let callee_generic_argument_map = self.type_visitor().get_generic_arguments_map(
                    def.did,
                    callee_generic_arguments,
                    &actual_argument_types,
                );
                let fun_ty = self.bv.tcx.type_of(destructor.did);
                let func_const = self
                    .visit_function_reference(destructor.did, fun_ty, Some(substs))
                    .clone();
                let func_to_call = Rc::new(func_const.clone().into());
                let destination = Some((*place, target));
                let ref_to_path_value = AbstractValue::make_reference(path);
                let mut call_visitor = CallVisitor::new(
                    self,
                    destructor.did,
                    Some(callee_generic_arguments),
                    callee_generic_argument_map.clone(),
                    self.bv.current_environment.clone(),
                    func_const,
                );
                call_visitor.actual_args = vec![(
                    Path::new_computed(ref_to_path_value.clone()),
                    ref_to_path_value,
                )];
                call_visitor.actual_argument_types = actual_argument_types;
                call_visitor.cleanup = unwind;
                call_visitor.destination = destination;
                call_visitor.callee_fun_val = func_to_call;
                let function_summary = call_visitor
                    .get_function_summary()
                    .unwrap_or_else(Summary::default);
                call_visitor.transfer_and_refine_into_current_environment(&function_summary);
                return;
            }
        }

        // Propagate the entry condition to the successor blocks.
        self.bv
            .current_environment
            .exit_conditions
            .insert_mut(target, self.bv.current_environment.entry_condition.clone());
        if let Some(unwind_target) = unwind {
            self.bv.current_environment.exit_conditions.insert_mut(
                unwind_target,
                self.bv.current_environment.entry_condition.clone(),
            );
        }
    }

    /// Block ends with the call of a function.
    ///
    /// #Arguments
    /// * `func` - The function that’s being called
    /// * `args` - Arguments the function is called with.
    /// These are owned by the callee, which is free to modify them.
    /// This allows the memory occupied by "by-value" arguments to be
    /// reused across function calls without duplicating the contents.
    /// * `destination` - Destination for the return value. If some, the call returns a value.
    /// * `cleanup` - Cleanups to be done if the call unwinds.
    /// * `from_hir_call` - Whether this is from a call in HIR, rather than from an overloaded
    /// operator. True for overloaded function call.
    #[logfn_inputs(TRACE)]
    fn visit_call(
        &mut self,
        func: &mir::Operand<'tcx>,
        args: &[mir::Operand<'tcx>],
        destination: &Option<(mir::Place<'tcx>, mir::BasicBlock)>,
        cleanup: Option<mir::BasicBlock>,
        from_hir_call: bool,
        fn_span: &rustc_span::Span,
    ) {
        // This offset is used to distinguish any local variables that leak out from the called function
        // from local variables of the callee function.
        // This situation arises when a structured value stored in a local variable is assigned to
        // a field reachable from a mutable parameter.
        // We assume that no program that does not make MIRAI run out of memory will have more than
        // a million local variables.
        self.bv.fresh_variable_offset += 1_000_000;

        trace!("source location {:?}", fn_span);
        trace!("call stack {:?}", self.bv.active_calls_map);
        trace!("visit_call {:?} {:?}", func, args);
        trace!(
            "self.generic_argument_map {:?}",
            self.type_visitor().generic_argument_map
        );
        trace!(
            "actual_argument_types {:?}",
            self.type_visitor().actual_argument_types
        );
        trace!("env {:?}", self.bv.current_environment);
        let func_to_call = self.visit_operand(func);
        let func_ref = self.get_func_ref(&func_to_call);
        let func_ref_to_call;
        if let Some(fr) = func_ref {
            func_ref_to_call = fr;
        } else {
            if self.might_be_reachable().unwrap_or(true)
                && self
                    .bv
                    .already_reported_errors_for_call_to
                    .insert(func_to_call)
            {
                self.report_missing_summary();
                warn!(
                        "function {} can't be reliably analyzed because it calls an unknown function. {:?}",
                        utils::summary_key_str(self.bv.tcx, self.bv.def_id),
                        self.bv.current_span
                    );
            }
            return;
        }
        let callee_def_id = func_ref_to_call
            .def_id
            .expect("callee obtained via operand should have def id");
        let substs = self
            .bv
            .cv
            .substs_cache
            .get(&callee_def_id)
            .expect("MIR should ensure this");
        let mut callee_generic_arguments = self
            .type_visitor()
            .specialize_substs(substs, &self.type_visitor().generic_argument_map);
        let actual_args: Vec<(Rc<Path>, Rc<AbstractValue>)> = args
            .iter()
            .map(|arg| (self.get_operand_path(arg), self.visit_operand(arg)))
            .collect();
        let actual_argument_types: Vec<Ty<'tcx>> = args
            .iter()
            .map(|arg| {
                let arg_ty = self.get_operand_rustc_type(arg);
                if utils::is_concrete(arg_ty.kind()) {
                    arg_ty
                } else {
                    let specialized_ty = self.type_visitor().specialize_generic_argument_type(
                        arg_ty,
                        &self.type_visitor().generic_argument_map,
                    );
                    if utils::is_concrete(specialized_ty.kind()) {
                        specialized_ty
                    } else {
                        let path = self.get_operand_path(arg);
                        self.type_visitor()
                            .get_path_rustc_type(&path, self.bv.current_span)
                    }
                }
            })
            .collect();
        let callee_generic_argument_map = self.type_visitor().get_generic_arguments_map(
            callee_def_id,
            callee_generic_arguments,
            &actual_argument_types,
        );
        // If the generic arguments include a Self argument, fix that up with the actual type
        // of the call (this information was not available when the constant defining the called
        // function was visited, so the cached specialized generic argument list created there
        // might not be specialized enough.
        if !actual_argument_types.is_empty() && !utils::are_concrete(callee_generic_arguments) {
            let fty = self.bv.tcx.type_of(callee_def_id);
            if let TyKind::FnDef(_, substs) = fty.kind() {
                for (i, generic_ty_arg) in substs.types().enumerate() {
                    if let TyKind::Param(t_par) = generic_ty_arg.kind() {
                        if t_par.name.as_str() == "Self" {
                            let mut gen_args: Vec<GenericArg<'_>> =
                                callee_generic_arguments.iter().collect();
                            gen_args[i] = self
                                .type_visitor()
                                .get_dereferenced_type(actual_argument_types[0])
                                .into();
                            callee_generic_arguments = self.bv.tcx.intern_substs(&gen_args);
                            break;
                        }
                    }
                }
            }
        }
        let self_ty_is_fn_ptr = if let Some(ty) = actual_argument_types.get(0) {
            let self_ty = self.type_visitor().get_dereferenced_type(ty);
            matches!(self_ty.kind(), TyKind::FnPtr(..))
        } else {
            false
        };
        let adt_map = self
            .type_visitor()
            .get_adt_map(&actual_args, &self.bv.current_environment);

        let known_name = func_ref_to_call.known_name;
        let func_const = ConstantDomain::Function(func_ref_to_call);
        let func_const_args =
            &self.get_function_constant_args(&actual_args, &actual_argument_types);
        let mut call_visitor = CallVisitor::new(
            self,
            callee_def_id,
            Some(callee_generic_arguments),
            callee_generic_argument_map.clone(),
            self.bv.current_environment.clone(),
            func_const,
        );
        call_visitor.actual_args = actual_args;
        call_visitor.actual_argument_types = actual_argument_types;
        call_visitor.cleanup = cleanup;
        call_visitor.destination = *destination;
        call_visitor.callee_fun_val = func_to_call;
        call_visitor.function_constant_args = func_const_args;
        call_visitor.initial_type_cache = adt_map;
        trace!("calling func {:?}", call_visitor.callee_func_ref);
        if call_visitor.handled_as_special_function_call() {
            return;
        }
        let function_summary = call_visitor
            .get_function_summary()
            .unwrap_or_else(Summary::default);

        if !function_summary.is_computed {
            if (known_name != KnownNames::StdCloneClone || !self_ty_is_fn_ptr)
                && call_visitor
                    .block_visitor
                    .bv
                    .already_reported_errors_for_call_to
                    .insert(call_visitor.callee_fun_val.clone())
            {
                call_visitor.block_visitor.report_missing_summary();
                if known_name != KnownNames::StdCloneClone
                    && !call_visitor.block_visitor.bv.analysis_is_incomplete
                {
                    return;
                }
            }
        } else if function_summary.is_incomplete
            && call_visitor
                .block_visitor
                .bv
                .already_reported_errors_for_call_to
                .insert(call_visitor.callee_fun_val.clone())
        {
            call_visitor.report_incomplete_summary();
        }

        if known_name == KnownNames::StdCloneClone {
            call_visitor.handle_clone(&function_summary);
        } else {
            call_visitor.transfer_and_refine_into_current_environment(&function_summary);
        }
    }

    #[logfn_inputs(TRACE)]
    pub fn get_function_constant_args(
        &self,
        actual_args: &[(Rc<Path>, Rc<AbstractValue>)],
        actual_arg_types: &[Ty<'tcx>],
    ) -> Vec<(Rc<Path>, Ty<'tcx>, Rc<AbstractValue>)> {
        let mut result = vec![];
        for (path, value) in self.bv.current_environment.value_map.iter() {
            if let Expression::CompileTimeConstant(ConstantDomain::Function(..)) = &value.expression
            {
                for (i, (arg_path, arg_val)) in actual_args.iter().enumerate() {
                    let is_arg_path = (*path) == *arg_path;
                    if is_arg_path || path.is_rooted_by(arg_path) {
                        let param_path_root = Path::new_parameter(i + 1);
                        let param_path = path.replace_root(arg_path, param_path_root);
                        let ty = if is_arg_path {
                            actual_arg_types[i]
                        } else {
                            self.type_visitor()
                                .get_path_rustc_type(path, self.bv.current_span)
                        };
                        if !ty.is_never() {
                            result.push((param_path, ty, value.clone()));
                        }
                        break;
                    } else {
                        match &arg_val.expression {
                            Expression::Reference(ipath)
                            | Expression::InitialParameterValue { path: ipath, .. }
                            | Expression::Variable { path: ipath, .. } => {
                                if (*path) == *ipath || path.is_rooted_by(ipath) {
                                    let mut param_path_root = Path::new_parameter(i + 1);
                                    if matches!(&arg_val.expression, Expression::Reference(..)) {
                                        let deref_type = self
                                            .type_visitor()
                                            .get_target_path_type(ipath, self.bv.current_span);
                                        param_path_root =
                                            Path::new_deref(param_path_root, deref_type);
                                    }
                                    let param_path = path.replace_root(ipath, param_path_root);
                                    let ty = self
                                        .type_visitor()
                                        .get_path_rustc_type(path, self.bv.current_span);
                                    result.push((param_path, ty, value.clone()));
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
            if let PathEnum::Computed { value: val }
            | PathEnum::HeapBlock { value: val }
            | PathEnum::Offset { value: val } = &path.value
            {
                if *val == *value {
                    if let Expression::CompileTimeConstant(ConstantDomain::Function(..)) =
                        &value.expression
                    {
                        let param_path = Path::new_parameter(i + 1);
                        let ty = actual_arg_types[i];
                        result.push((param_path, ty, value.clone()));
                    }
                }
            }
        }
        result
    }

    /// Give diagnostic, depending on self.bv.options.diag_level
    #[logfn_inputs(TRACE)]
    pub fn report_missing_summary(&mut self) {
        if self.might_be_reachable().unwrap_or(true) {
            if let Some(promotable_entry_condition) = self
                .bv
                .current_environment
                .entry_condition
                .extract_promotable_conjuncts(false)
            {
                if promotable_entry_condition.as_bool_if_known().is_none() {
                    let precondition = Precondition {
                        condition: promotable_entry_condition.logical_not(),
                        message: Rc::from("incomplete analysis of call because of a nested call to a function without a MIR body"),
                        provenance: None,
                        spans: vec![self.bv.current_span.source_callsite()],
                    };
                    self.bv.preconditions.push(precondition);
                    return;
                }
            }
            self.bv.analysis_is_incomplete = true;
            match self.bv.cv.options.diag_level {
                DiagLevel::Default => {
                    // In this mode we suppress any diagnostics about issues that might not be true
                    // positives.
                }
                _ => {
                    // Give a diagnostic about this call, and make it the programmer's problem.
                    let warning = self.bv.cv.session.struct_span_warn(
                        self.bv.current_span,
                        "the called function did not resolve to an implementation with a MIR body",
                    );
                    self.bv.emit_diagnostic(warning);
                }
            }
        }
    }

    /// Returns the function reference part of the value, if there is one.
    #[logfn_inputs(TRACE)]
    pub fn get_func_ref(&mut self, val: &Rc<AbstractValue>) -> Option<Rc<FunctionReference>> {
        let extract_func_ref = |c: &ConstantDomain| match c {
            ConstantDomain::Function(func_ref) => Some(func_ref.clone()),
            _ => None,
        };
        match &val.expression {
            Expression::CompileTimeConstant(c) => {
                return extract_func_ref(c);
            }
            Expression::Reference(path)
            | Expression::InitialParameterValue {
                path,
                var_type: ExpressionType::NonPrimitive,
            }
            | Expression::InitialParameterValue {
                path,
                var_type: ExpressionType::ThinPointer,
            }
            | Expression::Variable {
                path,
                var_type: ExpressionType::NonPrimitive,
            }
            | Expression::Variable {
                path,
                var_type: ExpressionType::ThinPointer,
            } => {
                let closure_ty = self
                    .type_visitor()
                    .get_path_rustc_type(path, self.bv.current_span);
                let mut specialized_closure_ty =
                    self.type_visitor().specialize_generic_argument_type(
                        closure_ty,
                        &self.type_visitor().generic_argument_map,
                    );
                if let TyKind::Opaque(def_id, substs) = specialized_closure_ty.kind() {
                    let substs = self
                        .type_visitor()
                        .specialize_substs(substs, &self.type_visitor().generic_argument_map);
                    self.bv.cv.substs_cache.insert(*def_id, substs);
                    let closure_ty = self.bv.tcx.type_of(*def_id);
                    let map = self
                        .type_visitor()
                        .get_generic_arguments_map(*def_id, substs, &[]);
                    specialized_closure_ty = self
                        .type_visitor()
                        .specialize_generic_argument_type(closure_ty, &map);
                }
                match specialized_closure_ty.kind() {
                    TyKind::Closure(def_id, substs) | TyKind::FnDef(def_id, substs) => {
                        return extract_func_ref(self.visit_function_reference(
                            *def_id,
                            specialized_closure_ty,
                            Some(substs),
                        ));
                    }
                    //todo: what about generators?
                    TyKind::Ref(_, ty, _) => {
                        let specialized_closure_ty =
                            self.type_visitor().specialize_generic_argument_type(
                                ty,
                                &self.type_visitor().generic_argument_map,
                            );
                        if let TyKind::Closure(def_id, substs) | TyKind::FnDef(def_id, substs) =
                            specialized_closure_ty.kind()
                        {
                            return extract_func_ref(self.visit_function_reference(
                                *def_id,
                                specialized_closure_ty,
                                Some(substs),
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

    pub fn get_char_const_val(&mut self, val: u128) -> Rc<AbstractValue> {
        self.bv.get_char_const_val(val)
    }

    pub fn get_i128_const_val(&mut self, val: i128) -> Rc<AbstractValue> {
        self.bv.get_i128_const_val(val)
    }

    pub fn get_u128_const_val(&mut self, val: u128) -> Rc<AbstractValue> {
        self.bv.get_u128_const_val(val)
    }

    /// Gets a constant integer of type `ty` with bit representation specified by `val`.
    /// `ty` might not be a 128-bit integer type, so this method extends/truncates the bit
    /// representation accordingly.
    pub fn get_int_const_val(&mut self, mut val: u128, ty: Ty<'tcx>) -> Rc<AbstractValue> {
        let param_env = self.type_visitor().get_param_env();
        let is_signed;
        if let Ok(ty_and_layout) = self.bv.tcx.layout_of(param_env.and(ty)) {
            is_signed = ty_and_layout.abi.is_signed();
            let size = ty_and_layout.size;
            if is_signed {
                val = size.sign_extend(val);
            } else {
                val = size.truncate(val);
            }
        } else {
            is_signed = ty.is_signed();
        }
        if is_signed {
            self.get_i128_const_val(val as i128)
        } else if ty.is_char() {
            self.get_char_const_val(val)
        } else {
            self.get_u128_const_val(val)
        }
    }

    /// Emit a diagnostic to the effect that the current call might violate a the given precondition
    /// of the called function. Use the provenance and spans of the precondition to point out related locations.
    #[logfn_inputs(TRACE)]
    pub fn emit_diagnostic_for_precondition(
        &mut self,
        precondition: &Precondition,
        condition: &Rc<AbstractValue>,
        warn: bool,
    ) {
        precondition!(self.bv.check_for_errors);
        // In non library|paranoid mode we don't want to complain if the condition or reachability depends on
        // a parameter, since it is assumed that an implicit precondition was intended by the author.
        if !matches!(
            self.bv.cv.options.diag_level,
            DiagLevel::Library | DiagLevel::Paranoid
        ) {
            match (
                self.bv
                    .current_environment
                    .entry_condition
                    .extract_promotable_conjuncts(false),
                condition.extract_promotable_disjuncts(false),
            ) {
                (Some(promotable_entry_cond), Some(promotable_condition))
                    if promotable_entry_cond.as_bool_if_known().is_none()
                        || promotable_condition.as_bool_if_known().is_none() =>
                {
                    return;
                }
                _ => {}
            }
        }
        let mut diagnostic = if warn && !precondition.message.starts_with("possible ") {
            Rc::from(format!("possible {}", precondition.message))
        } else {
            precondition.message.clone()
        };
        if precondition.spans.is_empty() {
            if let Some(provenance) = &precondition.provenance {
                let mut buffer = diagnostic.to_string();
                buffer.push_str(", defined in ");
                buffer.push_str(provenance.as_ref());
                diagnostic = Rc::from(buffer.as_str());
            }
        }
        let span = self.bv.current_span;
        let mut warning = self
            .bv
            .cv
            .session
            .struct_span_warn(span, diagnostic.as_ref());
        for pc_span in precondition.spans.iter() {
            let span_str = self
                .bv
                .tcx
                .sess
                .source_map()
                .span_to_diagnostic_string(*pc_span);
            if span_str.starts_with("/rustc/") {
                warning.span_note(*pc_span, &format!("related location {}", span_str));
            } else {
                warning.span_note(*pc_span, "related location");
            };
        }
        self.bv.emit_diagnostic(warning);
    }

    /// Extend the current post condition by the given `cond`. If none was set before,
    /// this will just set it for the first time. If there is already a post condition.
    /// we check whether it is safe to extend it. It is considered safe if the block where
    /// it was set dominates the existing one.
    #[logfn_inputs(TRACE)]
    pub fn try_extend_post_condition(&mut self, cond: &Rc<AbstractValue>) {
        precondition!(self.bv.check_for_errors);
        if let Some(promotable_condition) = cond.extract_promotable_conjuncts(true) {
            let this_block = self.bv.current_location.block;
            match (self.bv.post_condition.clone(), self.bv.post_condition_block) {
                (Some(last_cond), Some(last_block)) => {
                    let dominators = self.bv.mir.dominators();
                    if dominators.is_dominated_by(this_block, last_block) {
                        // We can extend the last condition as all paths to this condition
                        // lead over it
                        self.bv.post_condition = Some(last_cond.and(promotable_condition));
                        self.bv.post_condition_block = Some(this_block);
                    } else {
                        let span = self.bv.current_span;
                        let warning = self.bv.cv.session.struct_span_warn(
                            span,
                            "multiple post conditions must be on the same execution path",
                        );
                        self.bv.emit_diagnostic(warning);
                    }
                }
                (_, _) => {
                    self.bv.post_condition = Some(promotable_condition);
                    self.bv.post_condition_block = Some(this_block);
                }
            }
        }
    }

    /// Check if the given condition is reachable and true.
    /// If not, issue a warning subject to various conditions and return the message.
    #[logfn_inputs(TRACE)]
    pub fn check_special_function_condition(
        &mut self,
        cond: &Rc<AbstractValue>,
        message: &str,
        function_name: KnownNames,
    ) -> Option<Rc<str>> {
        precondition!(self.bv.check_for_errors);
        if cond.is_bottom()
            || (self.bv.analysis_is_incomplete
                && self.bv.cv.options.diag_level != DiagLevel::Paranoid)
        {
            return None;
        }
        let (cond_as_bool, entry_cond_as_bool) =
            self.bv.check_condition_value_and_reachability(cond);

        // If we never get here, rather call verify_unreachable!()
        if !entry_cond_as_bool.unwrap_or(true) {
            let span = self.bv.current_span.source_callsite();
            let message =
                "this is unreachable, mark it as such by using the verify_unreachable! macro";
            let warning = self.bv.cv.session.struct_span_warn(span, message);
            self.bv.emit_diagnostic(warning);
            return None;
        }

        // If the condition is always true when we get here there is nothing to report.
        if cond_as_bool.unwrap_or(false) {
            return None;
        }

        if function_name == KnownNames::MiraiPostcondition {
            let span = self.bv.current_span.source_callsite();
            let msg = if cond_as_bool.is_some() {
                "provably false postcondition"
            } else {
                "possible unsatisfied postcondition"
            };
            let warning = self.bv.cv.session.struct_span_warn(span, msg);
            self.bv.emit_diagnostic(warning);
            // Don't add the post condition to the summary
            return None;
        }

        let promotable_entry_condition = self
            .bv
            .current_environment
            .entry_condition
            .extract_promotable_conjuncts(false);

        // If a verification condition is always false, give an error since that is bad style.
        if function_name == KnownNames::MiraiVerify && !cond_as_bool.unwrap_or(true) {
            // If the condition is always false, give a style error
            let span = self.bv.current_span.source_callsite();
            let warning = self
                .bv
                .cv
                .session
                .struct_span_warn(span, "provably false verification condition");
            self.bv.emit_diagnostic(warning);
            if entry_cond_as_bool.is_none()
                && self.bv.preconditions.len() < k_limits::MAX_INFERRED_PRECONDITIONS
            {
                if let Some(promotable_entry_cond) = promotable_entry_condition {
                    // promote the path as a precondition. I.e. the program is only correct,
                    // albeit badly written, if we never get here.
                    let condition = promotable_entry_cond.logical_not();
                    let message = Rc::from(format!("possible {}", message));
                    let precondition = Precondition {
                        condition,
                        message,
                        provenance: None,
                        spans: vec![span],
                    };
                    self.bv.preconditions.push(precondition);
                }
            }
            return None;
        }

        let warning = format!("possible {}", message);

        // We might get here, or not, and the condition might be false, or not.
        // Give a warning if we don't know all of the callers, or if we run into a k-limit
        // or if the condition is not promotable or if the condition is being explicitly verified.
        let promotable_cond = cond.extract_promotable_disjuncts(false);
        if self.bv.function_being_analyzed_is_root()
            || self.bv.preconditions.len() >= k_limits::MAX_INFERRED_PRECONDITIONS
            || promotable_cond.is_none()
            || promotable_entry_condition.is_none()
            || function_name == KnownNames::MiraiVerify
        {
            // In non library|paranoid mode we don't want to complain if the condition or reachability depends on
            // a parameter, since it is assumed that an implicit precondition was intended by the author
            // unless, of course, the condition is being explicitly verified.
            if function_name == KnownNames::MiraiVerify
                || promotable_cond.is_none()
                || promotable_entry_condition.is_none()
                || matches!(
                    self.bv.cv.options.diag_level,
                    DiagLevel::Library | DiagLevel::Paranoid
                )
            {
                let span = self.bv.current_span.source_callsite();
                let warning = self.bv.cv.session.struct_span_warn(span, warning.as_str());
                self.bv.emit_diagnostic(warning);
            }
        }

        Some(Rc::from(warning.as_str()))
    }

    /// Check if the existence of a tag on the given value matches the expectation.
    /// If not, issue an error. If we cannot decide, issue a warning if the function is analyzed
    /// as a root, and promote the tag check as a precondition when possible.
    #[logfn_inputs(TRACE)]
    pub fn check_tag_existence_on_value(
        &mut self,
        value: &Rc<AbstractValue>,
        value_name: &str,
        tag: Tag,
        tag_name: &str,
        expecting_presence: bool,
    ) {
        precondition!(self.bv.check_for_errors);

        let tag_check = AbstractValue::make_tag_check(value.clone(), tag, expecting_presence);
        let (tag_check_as_bool, entry_cond_as_bool) =
            self.bv.check_condition_value_and_reachability(&tag_check);

        // We perform the tag check if the current block is possibly reachable.
        if entry_cond_as_bool.unwrap_or(true) {
            let promotable_entry_condition = self
                .bv
                .current_environment
                .entry_condition
                .extract_promotable_conjuncts(false);
            match tag_check_as_bool {
                None => {
                    // We cannot decide the result of the tag check.
                    // In this case, report a warning if we don't know all of the callers, we
                    // reach a k-limit, or the tag check contains a local variable so that we
                    // cannot promote it later as a precondition.
                    if self.bv.function_being_analyzed_is_root()
                        || self.bv.preconditions.len() >= k_limits::MAX_INFERRED_PRECONDITIONS
                    {
                        let span = self.bv.current_span.source_callsite();
                        let warning = self.bv.cv.session.struct_span_warn(
                            span,
                            format!("the {} may have a {} tag", value_name, tag_name).as_str(),
                        );
                        self.bv.emit_diagnostic(warning);
                    } else if promotable_entry_condition.is_none()
                        || tag_check.extract_promotable_disjuncts(false).is_none()
                    {
                        let span = self.bv.current_span.source_callsite();
                        let warning = self.bv.cv.session.struct_span_warn(
                            span,
                            format!(
                                "the {} may have a {} tag, \
                                and the tag check cannot be promoted as a precondition, \
                                because it contains local variables",
                                value_name, tag_name
                            )
                            .as_str(),
                        );
                        self.bv.emit_diagnostic(warning);
                    }
                }

                Some(tag_check_result) if !tag_check_result => {
                    // The existence of the tag on the value is different from the expectation.
                    // In this case, report an error.
                    let span = self.bv.current_span.source_callsite();
                    let warning = self.bv.cv.session.struct_span_warn(
                        span,
                        format!("the {} has a {} tag", value_name, tag_name).as_str(),
                    );
                    self.bv.emit_diagnostic(warning);
                }

                _ => {}
            }

            // We promote the tag check as a precondition if it is not always true, it does not
            // contain local variables, and we don't reach a k-limit.
            match (
                promotable_entry_condition,
                tag_check.extract_promotable_disjuncts(false),
            ) {
                (Some(promotable_entry_cond), Some(promotable_tag_check))
                    if !tag_check_as_bool.unwrap_or(false)
                        && self.bv.preconditions.len() < k_limits::MAX_INFERRED_PRECONDITIONS =>
                {
                    let condition = promotable_entry_cond.logical_not().or(promotable_tag_check);
                    let precondition = Precondition {
                        condition,
                        message: Rc::from(format!(
                            "the {} may have a {} tag",
                            value_name, tag_name
                        )),
                        provenance: None,
                        spans: vec![self.bv.current_span.source_callsite()],
                    };
                    self.bv.preconditions.push(precondition);
                }
                _ => {}
            }
        }
    }

    /// Jump to the target if the condition has the expected value,
    /// otherwise panic with a message and a cleanup target.
    #[logfn_inputs(TRACE)]
    fn visit_assert(
        &mut self,
        cond: &mir::Operand<'tcx>,
        expected: bool,
        msg: &mir::AssertMessage<'tcx>,
        target: mir::BasicBlock,
        cleanup: Option<mir::BasicBlock>,
    ) {
        // Propagate the entry condition to the successor blocks, conjoined with cond (or !cond).
        let cond_val = self.visit_operand(cond);
        let not_cond_val = cond_val.logical_not();
        if let Some(cleanup_target) = cleanup {
            let panic_exit_condition =
                self.bv
                    .current_environment
                    .entry_condition
                    .and(if expected {
                        not_cond_val.clone()
                    } else {
                        cond_val.clone()
                    });
            if !panic_exit_condition.is_bottom() {
                self.bv
                    .current_environment
                    .exit_conditions
                    .insert_mut(cleanup_target, panic_exit_condition);
            }
        };
        let normal_exit_condition = self
            .bv
            .current_environment
            .entry_condition
            .and(if expected {
                cond_val.clone()
            } else {
                not_cond_val
            });
        if !normal_exit_condition.is_bottom() {
            self.bv
                .current_environment
                .exit_conditions
                .insert_mut(target, normal_exit_condition);

            // Check the condition and issue a warning or infer a precondition.
            if self.bv.check_for_errors {
                if let mir::Operand::Constant(..) = cond {
                    // Do not complain about compile time constants known to the compiler.
                    // Leave that to the compiler.
                } else {
                    let (cond_as_bool_opt, entry_cond_as_bool) =
                        self.bv.check_condition_value_and_reachability(&cond_val);

                    // Quick exit if things are known.
                    if let Some(false) = entry_cond_as_bool {
                        // We can't reach this assertion, so just return.
                        return;
                    }
                    if let Some(cond_as_bool) = cond_as_bool_opt {
                        if expected == cond_as_bool {
                            // If the condition is always as expected when we get here, so there is nothing to report.
                            return;
                        }
                        // The condition is known to differ from expected so if we always get here if called,
                        // emit a diagnostic.
                        if entry_cond_as_bool.unwrap_or(false) {
                            let error = get_assert_msg_description(msg);
                            let span = self.bv.current_span;
                            let warning = self.bv.cv.session.struct_span_warn(span, error);
                            self.bv.emit_diagnostic(warning);
                            // No need to push a precondition, the caller can never satisfy it.
                            return;
                        }
                    }

                    // At this point, we don't know that this assert is unreachable and we don't know
                    // that the condition is as expected, so we need to warn about it somewhere.
                    let promotable_cond_val = cond_val.extract_promotable_disjuncts(false);
                    let promotable_entry_cond = self
                        .bv
                        .current_environment
                        .entry_condition
                        .extract_promotable_conjuncts(false);

                    if promotable_cond_val.is_none()
                        || promotable_entry_cond.is_none()
                        || self.bv.preconditions.len() >= k_limits::MAX_INFERRED_PRECONDITIONS
                        || (self.bv.function_being_analyzed_is_root()
                            && self.bv.cv.options.diag_level >= DiagLevel::Library)
                    {
                        // Can't make this the caller's problem.
                        let warning = format!("possible {}", get_assert_msg_description(msg));
                        let span = self.bv.current_span;
                        let warning = self.bv.cv.session.struct_span_warn(span, warning.as_str());
                        self.bv.emit_diagnostic(warning);
                        return;
                    }

                    // Make it the caller's problem by pushing a precondition.
                    // After, of course, removing any promoted preconditions that match the current
                    // source span.
                    let sp = self.bv.current_span;
                    self.bv
                        .preconditions
                        .retain(|pc| pc.spans.last() != Some(&sp));
                    let expected_cond = if expected {
                        promotable_cond_val.unwrap()
                    } else {
                        promotable_cond_val.unwrap().logical_not()
                    };
                    // To make sure that this assertion never fails, we should either never
                    // get here (!entry_condition) or expected_cond should be true.
                    let condition = promotable_entry_cond
                        .unwrap()
                        .logical_not()
                        .or(expected_cond);
                    let message = Rc::from(String::from(get_assert_msg_description(msg)));
                    let precondition = Precondition {
                        condition,
                        message,
                        provenance: None,
                        spans: vec![self.bv.current_span],
                    };
                    self.bv.preconditions.push(precondition);
                }
            }
        }

        fn get_assert_msg_description<'tcx>(msg: &mir::AssertMessage<'tcx>) -> &'tcx str {
            match msg {
                mir::AssertKind::BoundsCheck { .. } => "index out of bounds",
                _ => msg.description(),
            }
        }
    }

    /// Checks if the current entry condition is not known to be false.
    /// If the abstract domains are undecided, resort to using the SMT solver.
    /// Only call this when doing actual error checking, since this is expensive.
    #[logfn_inputs(TRACE)]
    #[logfn(TRACE)]
    pub fn might_be_reachable(&mut self) -> Option<bool> {
        trace!(
            "entry condition {:?}",
            self.bv.current_environment.entry_condition
        );
        let mut entry_cond_as_bool = self
            .bv
            .current_environment
            .entry_condition
            .as_bool_if_known();
        if entry_cond_as_bool.is_none() {
            // The abstract domains are unable to decide if the entry condition is always true or
            // always false.
            // See if the SMT solver can prove that the entry condition is always false.
            self.bv.smt_solver.set_backtrack_position();
            let smt_expr = {
                let ec = &self.bv.current_environment.entry_condition.expression;
                self.bv.smt_solver.get_as_smt_predicate(ec)
            };
            self.bv.smt_solver.assert(&smt_expr);
            if self.bv.smt_solver.solve() == SmtResult::Unsatisfiable {
                // The solver can prove that the entry condition is always false.
                entry_cond_as_bool = Some(false);
            }
            self.bv.smt_solver.backtrack();
        }
        entry_cond_as_bool
    }

    /// Execute a piece of inline Assembly.
    #[logfn_inputs(TRACE)]
    fn visit_inline_asm(&mut self, target: &Option<mir::BasicBlock>) {
        let span = self.bv.current_span;
        let warning = self
            .bv
            .cv
            .session
            .struct_span_warn(span, "Inline assembly code cannot be analyzed by MIRAI.");
        self.bv.emit_diagnostic(warning);
        self.bv.analysis_is_incomplete = true;
        if let Some(target) = target {
            // Propagate the entry condition to the successor block.
            self.bv
                .current_environment
                .exit_conditions
                .insert_mut(*target, self.bv.current_environment.entry_condition.clone());
        }
    }

    /// Calls a specialized visitor for each kind of Rvalue
    #[logfn_inputs(TRACE)]
    fn visit_rvalue(&mut self, path: Rc<Path>, rvalue: &mir::Rvalue<'tcx>) {
        match rvalue {
            mir::Rvalue::Use(operand) => {
                self.visit_use(path, operand);
            }
            mir::Rvalue::Repeat(operand, count) => {
                self.visit_repeat(path, operand, count);
            }
            mir::Rvalue::Ref(_, _, place) | mir::Rvalue::AddressOf(_, place) => {
                self.visit_address_of(path, place);
            }
            mir::Rvalue::ThreadLocalRef(def_id) => {
                self.visit_thread_local_ref(path, *def_id);
            }
            mir::Rvalue::Len(place) => {
                self.visit_len(path, place);
            }
            mir::Rvalue::Cast(cast_kind, operand, ty) => {
                let specialized_ty = self.type_visitor().specialize_generic_argument_type(
                    ty,
                    &self.type_visitor().generic_argument_map,
                );
                self.visit_cast(path, *cast_kind, operand, specialized_ty);
            }
            mir::Rvalue::BinaryOp(bin_op, box (left_operand, right_operand)) => {
                self.visit_binary_op(path, *bin_op, left_operand, right_operand);
            }
            mir::Rvalue::CheckedBinaryOp(bin_op, box (left_operand, right_operand)) => {
                self.visit_checked_binary_op(path, *bin_op, left_operand, right_operand);
            }
            mir::Rvalue::NullaryOp(null_op, ty) => {
                let specialized_ty = self.type_visitor().specialize_generic_argument_type(
                    ty,
                    &self.type_visitor().generic_argument_map,
                );
                self.visit_nullary_op(path, *null_op, specialized_ty);
            }
            mir::Rvalue::UnaryOp(unary_op, operand) => {
                self.visit_unary_op(path, *unary_op, operand);
            }
            mir::Rvalue::Discriminant(place) => {
                self.visit_discriminant(path, place);
            }
            mir::Rvalue::Aggregate(aggregate_kinds, operands) => {
                self.visit_aggregate(path, aggregate_kinds, operands);
            }
        }
    }

    /// path = x (either a move or copy, depending on type of x), or path = constant.
    #[logfn_inputs(TRACE)]
    fn visit_use(&mut self, path: Rc<Path>, operand: &mir::Operand<'tcx>) {
        match operand {
            mir::Operand::Copy(place) => {
                self.visit_used_copy(path, place);
            }
            mir::Operand::Move(place) => {
                self.visit_used_move(path, place);
            }
            mir::Operand::Constant(constant) => {
                let mir::Constant { literal, .. } = constant.borrow();
                let rh_type = literal.ty();
                let const_value = self.visit_literal(literal);
                if const_value.expression.infer_type() == ExpressionType::NonPrimitive {
                    // Transfer children into the environment, discard const_value.
                    if let Expression::Reference(rpath) | Expression::Variable { path: rpath, .. } =
                        &const_value.expression
                    {
                        self.bv
                            .copy_or_move_elements(path, rpath.clone(), rh_type, false);
                        return;
                    }
                }

                match &const_value.expression {
                    Expression::HeapBlock { .. } => {
                        let rpath = Rc::new(
                            PathEnum::HeapBlock {
                                value: const_value.clone(),
                            }
                            .into(),
                        );
                        self.bv.copy_or_move_elements(path, rpath, rh_type, false);
                    }
                    _ => {
                        let rpath = Path::new_computed(const_value.clone());
                        self.bv.copy_or_move_elements(path, rpath, rh_type, false);
                    }
                }
            }
        };
    }

    /// For each (path', value) pair in the environment where path' is rooted in place,
    /// add a (path'', value) pair to the environment where path'' is a copy of path re-rooted
    /// with place.
    #[logfn_inputs(TRACE)]
    fn visit_used_copy(&mut self, target_path: Rc<Path>, place: &mir::Place<'tcx>) {
        let rpath = self.visit_rh_place(place);
        let rtype = self
            .type_visitor()
            .get_rustc_place_type(place, self.bv.current_span);
        let target_type = self
            .type_visitor()
            .get_path_rustc_type(&target_path, self.bv.current_span);
        if !utils::is_concrete(target_type.kind()) {
            let source_type = self
                .type_visitor()
                .get_path_rustc_type(&rpath, self.bv.current_span);
            if utils::is_concrete(source_type.kind()) {
                debug!(
                    "changing {:?} from {:?} to {:?}",
                    target_path, target_type, source_type
                );
                self.type_visitor_mut()
                    .set_path_rustc_type(target_path.clone(), source_type);
            }
        }
        self.bv
            .copy_or_move_elements(target_path, rpath, rtype, false);
    }

    /// For each (path', value) pair in the environment where path' is rooted in place,
    /// add a (path'', value) pair to the environment where path'' is a copy of path re-rooted
    /// with place, and also remove the (path', value) pair from the environment.
    #[logfn_inputs(TRACE)]
    fn visit_used_move(&mut self, target_path: Rc<Path>, place: &mir::Place<'tcx>) {
        let rpath = self.visit_rh_place(place);
        let rtype = self
            .type_visitor()
            .get_rustc_place_type(place, self.bv.current_span);
        let target_type = self
            .type_visitor()
            .get_path_rustc_type(&target_path, self.bv.current_span);
        if !utils::is_concrete(target_type.kind()) {
            let source_type = self
                .type_visitor()
                .get_path_rustc_type(&rpath, self.bv.current_span);
            if utils::is_concrete(source_type.kind()) {
                debug!(
                    "changing {:?} from {:?} to {:?}",
                    target_path, target_type, source_type
                );
                self.type_visitor_mut()
                    .set_path_rustc_type(target_path.clone(), source_type);
            }
        }
        self.bv
            .copy_or_move_elements(target_path, rpath, rtype, true);
    }

    /// path = [x; 32]
    #[logfn_inputs(TRACE)]
    fn visit_repeat(&mut self, path: Rc<Path>, operand: &mir::Operand<'tcx>, count: &Const<'tcx>) {
        let length_path = Path::new_length(path.clone());
        let length_value = self.visit_const(count);
        self.bv
            .current_environment
            .update_value_at(length_path, length_value.clone());
        let slice_path = Path::new_slice(path, length_value);
        let initial_value = self.visit_operand(operand);
        self.bv
            .current_environment
            .update_value_at(slice_path, initial_value);
    }

    /// path = &x or &mut x or &raw const x
    #[logfn_inputs(TRACE)]
    fn visit_address_of(&mut self, path: Rc<Path>, place: &mir::Place<'tcx>) {
        let target_type = self
            .type_visitor()
            .get_path_rustc_type(&path, self.bv.current_span);
        let source_type = self
            .type_visitor()
            .get_rustc_place_type(place, self.bv.current_span);
        let value_path = self.visit_lh_place(place);
        let value = match &value_path.value {
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } if *selector.as_ref() == PathSelector::Deref => {
                if source_type.is_box() {
                    // taking the address of the thing in the box, which is, of course, a pointer.
                    // Special case this because we want that pointer, not a pointer to the pointer
                    // Use copy_or_move_elements because the pointer could be fat.
                    self.bv.copy_or_move_elements(
                        path,
                        qualifier.canonicalize(&self.bv.current_environment),
                        target_type,
                        false,
                    );
                    return;
                }

                // We are taking a reference to the result of a deref. This is a bit awkward.
                // The deref, by itself, essentially does a copy of the value denoted by the qualifier.
                // When combined with an address_of operation, however, things are more complicated.
                // If the contents at offset 0 from the target of the pointer being dereferenced is
                // a fat (slice) pointer then the address_of operation results in a copy of the fat pointer.
                // We check for this by looking at the type of the operation result target.
                if self.type_visitor().is_slice_pointer(target_type.kind()) {
                    // If we get here we are effectively copying to a fat pointer without a cast,
                    // so there is no type information to use to come up with the length part of
                    // the fat pointer. This implies that the source value must itself be a fat
                    // pointer. This is, however, not what we'll see if we get the type of the
                    // qualifier path. The reason for that is the ambiguous semantics of the
                    // deref operator: Mostly, doing a deref of a fat pointer means doing a
                    // deref of the thin pointer since that is what we expect when de-referencing
                    // a pointer, whether it is fat or thin.
                    //
                    // When combined with an address_of operator, however, deref just means to
                    // copy the pointer, fat or thin. (In this case, it must be fat.)
                    // When the qualifier was constructed, however, this contextual bit information
                    // was not known, so qualifier would have been modified to select the thin
                    // pointer. Undo the damage by stripping off the field 0, since we now know
                    // that we want to copy the fat pointer.
                    if let PathEnum::QualifiedPath {
                        qualifier,
                        selector,
                        ..
                    } = &qualifier.value
                    {
                        if matches!(selector.as_ref(), PathSelector::Field(0)) {
                            self.bv.copy_or_move_elements(
                                path,
                                qualifier.canonicalize(&self.bv.current_environment),
                                target_type,
                                false,
                            );
                            return;
                        }
                    }
                    // Well, this is awkward. Qualifier was not known to be a fat pointer when
                    // the deref path was constructed. That seems all sorts of wrong.
                    warn!(
                        "deref failed to turn a fat pointer into a thin pointer {:?}",
                        self.bv.current_span
                    );
                    // Nevertheless, it happens, so until all the cases are identified and
                    // debugged, assume that qualifier corresponds to a fat pointer and that
                    // copy_or_move_elements will populate the target path with the necessary information.
                    // If that information is not actually there, this results in a conservative over approximation.
                }
                // If the target is not a fat pointer, it must be a thin pointer since an
                // address of operator can hardly result in anything else. So, in this case,
                // &*source_thin_ptr should just be a non canonical alias for source_thin_ptr.
                self.bv.copy_or_move_elements(
                    path,
                    qualifier.canonicalize(&self.bv.current_environment),
                    target_type,
                    false,
                );
                return;
            }
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } if matches!(selector.as_ref(), PathSelector::Field(0)) => {
                let qty = self
                    .type_visitor()
                    .get_path_rustc_type(qualifier, self.bv.current_span);
                let unwrapped_qty = self.type_visitor().remove_transparent_wrappers(qty);
                match &qualifier.value {
                    PathEnum::QualifiedPath {
                        qualifier,
                        selector,
                        ..
                    } if *selector.as_ref() == PathSelector::Deref => {
                        if qty != unwrapped_qty {
                            AbstractValue::make_reference(qualifier.clone())
                        } else {
                            AbstractValue::make_reference(
                                value_path.canonicalize(&self.bv.current_environment),
                            )
                        }
                    }
                    _ => AbstractValue::make_reference(
                        value_path.canonicalize(&self.bv.current_environment),
                    ),
                }
            }
            PathEnum::Computed { .. }
            | PathEnum::Offset { .. }
            | PathEnum::QualifiedPath { .. } => {
                AbstractValue::make_reference(value_path.canonicalize(&self.bv.current_environment))
            }
            PathEnum::PromotedConstant { .. } => {
                if let Some(val) = self.bv.current_environment.value_at(&value_path) {
                    if let Expression::HeapBlock { .. } = &val.expression {
                        let heap_path = Rc::new(PathEnum::HeapBlock { value: val.clone() }.into());
                        AbstractValue::make_reference(heap_path)
                    } else {
                        AbstractValue::make_reference(value_path.clone())
                    }
                } else {
                    AbstractValue::make_reference(value_path.clone())
                }
            }
            PathEnum::HeapBlock { value } => value.clone(),
            _ => AbstractValue::make_reference(value_path.clone()),
        };
        self.bv.current_environment.update_value_at(path, value);
    }

    /// Accessing a thread local static. This is inherently a runtime operation, even if llvm
    /// treats it as an access to a static. This `Rvalue` yields a reference to the thread local
    /// static.
    fn visit_thread_local_ref(&mut self, path: Rc<Path>, def_id: DefId) {
        let static_var = if self.bv.tcx.is_mir_available(def_id) {
            self.bv.import_static(Path::new_static(self.bv.tcx, def_id))
        } else {
            Path::new_static(self.bv.tcx, def_id)
        };
        self.bv
            .current_environment
            .update_value_at(path, AbstractValue::make_reference(static_var));
    }

    /// path = length of a [X] or [X;n] value.
    #[logfn_inputs(TRACE)]
    fn visit_len(&mut self, path: Rc<Path>, place: &mir::Place<'tcx>) {
        let place_ty = self
            .type_visitor()
            .get_rustc_place_type(place, self.bv.current_span);
        let len_value = if let TyKind::Array(_, len) = place_ty.kind() {
            // We only get here if "-Z mir-opt-level=0" was specified.
            // With more optimization the len instruction becomes a constant.
            self.visit_const(len)
        } else {
            // In this case place type must be a slice.
            let mut value_path = self.visit_lh_place(place);
            if let PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } = &value_path.value
            {
                if let PathSelector::Deref = selector.as_ref() {
                    // De-referencing a slice pointer is normally the same as de-referencing its
                    // thin pointer, so self.visit_lh_place above assumed that much and will have
                    // added in a field 0 selector before the deref.
                    // In this context, however, we want the length of the slice pointer,
                    // so we need to drop the thin pointer field selector.
                    if let PathEnum::QualifiedPath {
                        qualifier,
                        selector,
                        ..
                    } = &qualifier.value
                    {
                        if matches!(selector.as_ref(), PathSelector::Field(0)) {
                            value_path = qualifier.clone();
                        }
                    }
                } else {
                    assume_unreachable!("{:?}", selector);
                }
            }
            let length_path =
                Path::new_length(value_path).canonicalize(&self.bv.current_environment);
            self.bv
                .lookup_path_and_refine_result(length_path, self.bv.tcx.types.usize)
        };
        self.bv.current_environment.update_value_at(path, len_value);
    }

    /// path = operand as ty.
    #[logfn_inputs(TRACE)]
    fn visit_cast(
        &mut self,
        path: Rc<Path>,
        cast_kind: mir::CastKind,
        operand: &mir::Operand<'tcx>,
        ty: rustc_middle::ty::Ty<'tcx>,
    ) {
        match cast_kind {
            mir::CastKind::Pointer(pointer_cast) => {
                // The value remains unchanged, but pointers may be fat, so use copy_or_move_elements
                let (is_move, place) = match operand {
                    mir::Operand::Copy(place) => (false, place),
                    mir::Operand::Move(place) => (true, place),
                    mir::Operand::Constant(..) => {
                        // Compile time constant pointers can arise from first class function values.
                        // Such pointers are thin.
                        let result = self.visit_operand(operand);
                        self.bv.current_environment.update_value_at(path, result);
                        return;
                    }
                };
                if let PointerCast::Unsize = pointer_cast {
                    // Unsize a pointer/reference value, e.g., `&[T; n]` to
                    // `&[T]`. Note that the source could be a thin or fat pointer.
                    // This will do things like convert thin pointers to fat
                    // pointers, or convert structs containing thin pointers to
                    // structs containing fat pointers, or convert between fat
                    // pointers. We don't store the details of how the transform is
                    // done (in fact, we don't know that, because it might depend on
                    // the precise type parameters). We just store the target
                    // type. Codegen backends and miri figure out what has to be done
                    // based on the precise source/target type at hand.
                    //
                    // We do this by iterating over all paths in the environment rooted in
                    // source_path and upgrading thin pointers to fat pointers if the re-rooted
                    // path to the thin pointer infers to a type that is a slice pointer.
                    let value_map = self.bv.current_environment.value_map.clone();
                    let source_path = self.visit_lh_place(place);
                    if !utils::is_concrete(ty.kind()) {
                        let source_type = self
                            .type_visitor()
                            .get_path_rustc_type(&source_path, self.bv.current_span);
                        if utils::is_concrete(source_type.kind()) {
                            debug!("changing {:?} from {:?} to {:?}", path, ty, source_type);
                            self.type_visitor_mut()
                                .set_path_rustc_type(path.clone(), source_type);
                        }
                    }
                    for (p, value) in value_map
                        .iter()
                        .filter(|(p, _)| source_path == **p || p.is_rooted_by(&source_path))
                    {
                        let target_path = p
                            .replace_root(&source_path, path.clone())
                            .canonicalize(&self.bv.current_environment);
                        if value.expression.infer_type() != ExpressionType::ThinPointer {
                            // just copy
                            self.bv
                                .current_environment
                                .update_value_at(target_path, value.clone());
                        } else {
                            let target_type = self
                                .type_visitor()
                                .get_path_rustc_type(&target_path, self.bv.current_span);
                            if self.type_visitor().is_slice_pointer(target_type.kind()) {
                                // convert the source thin pointer to a fat pointer if the target path is a slice pointer
                                let thin_pointer_path = Path::new_field(target_path.clone(), 0);
                                self.bv
                                    .current_environment
                                    .update_value_at(thin_pointer_path, value.clone());
                                let source_type = self
                                    .type_visitor()
                                    .get_path_rustc_type(p, self.bv.current_span);
                                if let TyKind::Array(_, len) = self
                                    .type_visitor()
                                    .get_dereferenced_type(source_type)
                                    .kind()
                                {
                                    let length_path = Path::new_length(target_path);
                                    let length_value = self.visit_const(len);
                                    self.bv
                                        .current_environment
                                        .update_value_at(length_path, length_value);
                                } else {
                                    assume_unreachable!(
                                        "non array thin pointer type {:?}",
                                        source_type
                                    );
                                }
                            } else {
                                // just copy
                                self.bv
                                    .current_environment
                                    .update_value_at(target_path, value.clone());
                            }
                        }
                    }
                    return;
                }
                let source_path = self.visit_rh_place(place);
                self.bv
                    .copy_or_move_elements(path, source_path, ty, is_move);
            }
            mir::CastKind::Misc => {
                let source_value = self.visit_operand(operand);
                let source_type = self.get_operand_rustc_type(operand);
                let result = source_value.cast(ExpressionType::from(ty.kind(), self.bv.tcx));
                if let mir::Operand::Move(place) = operand {
                    let source_path = self.visit_rh_place(place);
                    self.bv.current_environment.value_map =
                        self.bv.current_environment.value_map.remove(&source_path);
                }
                if result != source_value || (source_type.is_trait() && !ty.is_trait()) {
                    self.type_visitor_mut()
                        .set_path_rustc_type(Path::get_as_path(result.clone()), ty);
                }
                self.bv.current_environment.update_value_at(path, result);
            }
        }
    }

    /// Apply the given binary operator to the two operands and assign result to path.
    #[logfn_inputs(TRACE)]
    fn visit_binary_op(
        &mut self,
        path: Rc<Path>,
        bin_op: mir::BinOp,
        left_operand: &mir::Operand<'tcx>,
        right_operand: &mir::Operand<'tcx>,
    ) {
        let left = self.visit_operand(left_operand);
        let right = self.visit_operand(right_operand);
        let result = match bin_op {
            mir::BinOp::Add => left.addition(right),
            mir::BinOp::BitAnd => left.bit_and(right),
            mir::BinOp::BitOr => left.bit_or(right),
            mir::BinOp::BitXor => left.bit_xor(right),
            mir::BinOp::Div => left.divide(right),
            mir::BinOp::Eq => left.equals(right),
            mir::BinOp::Ge => left.greater_or_equal(right),
            mir::BinOp::Gt => left.greater_than(right),
            mir::BinOp::Le => left.less_or_equal(right),
            mir::BinOp::Lt => left.less_than(right),
            mir::BinOp::Mul => left.multiply(right),
            mir::BinOp::Ne => left.not_equals(right),
            mir::BinOp::Offset => left.offset(right),
            mir::BinOp::Rem => left.remainder(right),
            mir::BinOp::Shl => left.shift_left(right),
            mir::BinOp::Shr => {
                // We assume that path is a temporary used to track the operation result.
                let target_type = self
                    .type_visitor()
                    .get_target_path_type(&path, self.bv.current_span);
                left.shr(right, target_type)
            }
            mir::BinOp::Sub => left.subtract(right),
        };
        self.bv.current_environment.update_value_at(path, result);
    }

    /// Apply the given binary operator to the two operands, with overflow checking where appropriate
    /// and assign the result to path.
    #[logfn_inputs(TRACE)]
    fn visit_checked_binary_op(
        &mut self,
        path: Rc<Path>,
        bin_op: mir::BinOp,
        left_operand: &mir::Operand<'tcx>,
        right_operand: &mir::Operand<'tcx>,
    ) {
        // We assume that path is a temporary used to track the operation result and its overflow status.
        let target_type = self
            .type_visitor()
            .get_first_part_of_target_path_type_tuple(&path, self.bv.current_span);
        let left = self.visit_operand(left_operand);
        let right = self.visit_operand(right_operand);
        let (result, overflow_flag) = Self::do_checked_binary_op(bin_op, target_type, left, right);
        let path0 = Path::new_field(path.clone(), 0);
        self.bv.current_environment.update_value_at(path0, result);
        let path1 = Path::new_field(path, 1);
        self.bv
            .current_environment
            .update_value_at(path1, overflow_flag);
    }

    /// Apply the given binary operator to the two operands, with overflow checking where appropriate
    #[logfn_inputs(TRACE)]
    pub fn do_checked_binary_op(
        bin_op: mir::BinOp,
        target_type: ExpressionType,
        left: Rc<AbstractValue>,
        right: Rc<AbstractValue>,
    ) -> (Rc<AbstractValue>, Rc<AbstractValue>) {
        let (result, overflow_flag) = match bin_op {
            mir::BinOp::Add => (
                left.addition(right.clone()),
                left.add_overflows(right, target_type),
            ),
            mir::BinOp::Mul => (
                left.multiply(right.clone()),
                left.mul_overflows(right, target_type),
            ),
            mir::BinOp::Shl => (
                left.shift_left(right.clone()),
                left.shl_overflows(right, target_type),
            ),
            mir::BinOp::Shr => (
                left.shr(right.clone(), target_type.clone()),
                left.shr_overflows(right, target_type),
            ),
            mir::BinOp::Sub => (
                left.subtract(right.clone()),
                left.sub_overflows(right, target_type),
            ),
            _ => assume_unreachable!(),
        };
        (result, overflow_flag)
    }

    /// Create a value based on the given type and assign it to path.
    #[logfn_inputs(TRACE)]
    fn visit_nullary_op(
        &mut self,
        mut path: Rc<Path>,
        null_op: mir::NullOp,
        ty: rustc_middle::ty::Ty<'tcx>,
    ) {
        let param_env = self.type_visitor().get_param_env();
        let (len, alignment) = if let Ok(ty_and_layout) = self.bv.tcx.layout_of(param_env.and(ty)) {
            let layout = ty_and_layout.layout;
            (
                Rc::new((layout.size.bytes() as u128).into()),
                Rc::new((layout.align.abi.bytes() as u128).into()),
            )
        } else {
            let type_index = self.type_visitor().get_index_for(self.bv.tcx.types.u128);
            //todo: need expressions that eventually refines into the actual layout size/alignment
            (
                AbstractValue::make_typed_unknown(
                    ExpressionType::U128,
                    Path::new_local(998, type_index),
                ),
                AbstractValue::make_typed_unknown(
                    ExpressionType::U128,
                    Path::new_local(997, type_index),
                ),
            )
        };
        let value = match null_op {
            mir::NullOp::Box => {
                // The box is a struct that is located at path.
                // It contains a pointer at field 0, which is a struct of type Unique,
                // which contains the pointer that points to the new heap block.
                // This instruction only allocates the heap block
                // and fills in the box pointer. The initialization of the heap block is done
                // in a subsequent MIR instruction of the form (*box) = box_value. De-referencing
                // a box structure amounts to de-referencing the pointer in field 0.
                path = Path::new_field(path, 0);
                AbstractValue::make_reference(Path::get_as_path(
                    self.bv.get_new_heap_block(len, alignment, false, ty),
                ))
            }
            mir::NullOp::SizeOf => len,
        };
        self.bv.current_environment.update_value_at(path, value);
    }

    /// Apply the given unary operator to the operand and assign to path.
    #[logfn_inputs(TRACE)]
    fn visit_unary_op(&mut self, path: Rc<Path>, un_op: mir::UnOp, operand: &mir::Operand<'tcx>) {
        let operand = self.visit_operand(operand);
        let result = match un_op {
            mir::UnOp::Neg => operand.negate(),
            mir::UnOp::Not => {
                let result_type = self
                    .type_visitor()
                    .get_target_path_type(&path, self.bv.current_span);
                if result_type.is_integer() {
                    operand.bit_not(result_type)
                } else {
                    operand.logical_not()
                }
            }
        };
        self.bv.current_environment.update_value_at(path, result);
    }

    /// Read the discriminant of an enum and assign to path.
    #[logfn_inputs(TRACE)]
    fn visit_discriminant(&mut self, path: Rc<Path>, place: &mir::Place<'tcx>) {
        let discriminant_path = Path::new_discriminant(self.visit_rh_place(place));
        let discriminant_value = self
            .bv
            .lookup_path_and_refine_result(discriminant_path, self.bv.tcx.types.u128);
        self.bv
            .current_environment
            .update_value_at(path, discriminant_value);
    }

    /// Currently only survives in the MIR that MIRAI sees, if the aggregate is an array.
    /// See https://github.com/rust-lang/rust/issues/48193.
    /// Copies the values from the operands to the target path and sets the length field.
    /// The target path identifies stack storage for the array and is not a fat pointer to the heap.
    #[logfn_inputs(TRACE)]
    fn visit_aggregate(
        &mut self,
        path: Rc<Path>,
        aggregate_kinds: &mir::AggregateKind<'tcx>,
        operands: &[mir::Operand<'tcx>],
    ) {
        precondition!(matches!(aggregate_kinds, mir::AggregateKind::Array(..)));
        let length_path = Path::new_length(path.clone());
        let length_value = self.get_u128_const_val(operands.len() as u128);
        self.bv
            .current_environment
            .update_value_at(length_path, length_value);
        for (i, operand) in operands.iter().enumerate() {
            let index_value = self.get_u128_const_val(i as u128);
            let index_path = Path::new_index(path.clone(), index_value);
            self.visit_used_operand(index_path, operand);
        }
    }

    /// Operand defines the values that can appear inside an rvalue. They are intentionally
    /// limited to prevent rvalues from being nested in one another.
    /// A used operand must move or copy values to a target path.
    #[logfn_inputs(TRACE)]
    fn visit_used_operand(&mut self, target_path: Rc<Path>, operand: &mir::Operand<'tcx>) {
        match operand {
            mir::Operand::Copy(place) => {
                self.visit_used_copy(target_path, place);
            }
            mir::Operand::Move(place) => {
                self.visit_used_move(target_path, place);
            }
            mir::Operand::Constant(constant) => {
                let mir::Constant { literal, .. } = constant.borrow();
                let const_value = self.visit_literal(literal);
                self.bv
                    .current_environment
                    .update_value_at(target_path, const_value);
            }
        };
    }

    /// Returns the path (location/lh-value) of the given operand.
    #[logfn_inputs(TRACE)]
    fn get_operand_path(&mut self, operand: &mir::Operand<'tcx>) -> Rc<Path> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => self.visit_rh_place(place),
            mir::Operand::Constant(..) => Path::new_computed(self.visit_operand(operand)),
        }
    }

    /// Returns the rustc Ty of the given operand.
    #[logfn_inputs(TRACE)]
    fn get_operand_rustc_type(&mut self, operand: &mir::Operand<'tcx>) -> Ty<'tcx> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => self
                .type_visitor()
                .get_rustc_place_type(place, self.bv.current_span),
            mir::Operand::Constant(constant) => {
                let mir::Constant { literal, .. } = constant.borrow();
                literal.ty()
            }
        }
    }

    /// Operand defines the values that can appear inside an rvalue. They are intentionally
    /// limited to prevent rvalues from being nested in one another.
    #[logfn_inputs(TRACE)]
    fn visit_operand(&mut self, operand: &mir::Operand<'tcx>) -> Rc<AbstractValue> {
        match operand {
            mir::Operand::Copy(place) => self.visit_copy(place),
            mir::Operand::Move(place) => self.visit_move(place),
            mir::Operand::Constant(constant) => {
                let mir::Constant { literal, .. } = constant.borrow();
                self.visit_literal(literal)
            }
        }
    }

    /// Copy: The value must be available for use afterwards.
    ///
    /// This implies that the type of the place must be `Copy`; this is true
    /// by construction during build, but also checked by the MIR type checker.
    #[logfn_inputs(TRACE)]
    fn visit_copy(&mut self, place: &mir::Place<'tcx>) -> Rc<AbstractValue> {
        let path = self.visit_rh_place(place);
        let rust_place_type = self
            .type_visitor()
            .get_rustc_place_type(place, self.bv.current_span);
        self.bv.lookup_path_and_refine_result(path, rust_place_type)
    }

    /// Move: The value (including old borrows of it) will not be used again.
    ///
    /// Safe for values of all types (modulo future developments towards `?Move`).
    /// Correct usage patterns are enforced by the borrow checker for safe code.
    /// `Copy` may be converted to `Move` to enable "last-use" optimizations.
    #[logfn_inputs(TRACE)]
    fn visit_move(&mut self, place: &mir::Place<'tcx>) -> Rc<AbstractValue> {
        let path = self.visit_rh_place(place);
        let rust_place_type = self
            .type_visitor()
            .get_rustc_place_type(place, self.bv.current_span);
        self.bv.lookup_path_and_refine_result(path, rust_place_type)
    }

    /// Returns a value that corresponds to the given literal
    #[logfn_inputs(TRACE)]
    pub fn visit_literal(&mut self, literal: &mir::ConstantKind<'tcx>) -> Rc<AbstractValue> {
        if let Some(v) = literal.try_to_value() {
            self.visit_const_kind(ConstKind::Value(v), literal.ty())
        } else if let Some(c) = literal.const_for_ty() {
            self.visit_const(c)
        } else {
            unreachable!("try_to_value will only return None when const_for_ty will return Some")
        }
    }

    /// Synthesizes a constant value. Also used for static variable values.
    #[logfn_inputs(TRACE)]
    pub fn visit_const(&mut self, literal: &Const<'tcx>) -> Rc<AbstractValue> {
        self.visit_const_kind(literal.val, literal.ty)
    }

    fn visit_const_kind(&mut self, mut val: ConstKind<'tcx>, lty: Ty<'tcx>) -> Rc<AbstractValue> {
        if let rustc_middle::ty::ConstKind::Unevaluated(Unevaluated {
            def: def_ty,
            substs,
            promoted,
        }) = &val
        {
            if def_ty.const_param_did.is_some() {
                val = val.eval(self.bv.tcx, self.type_visitor().get_param_env());
            } else {
                let mut def_id = def_ty.def_id_for_type_of();
                let substs = self
                    .type_visitor()
                    .specialize_substs(substs, &self.type_visitor().generic_argument_map);
                self.bv.cv.substs_cache.insert(def_id, substs);
                let path = match promoted {
                    Some(promoted) => {
                        let index = promoted.index();
                        Rc::new(PathEnum::PromotedConstant { ordinal: index }.into())
                    }
                    None => {
                        if !substs.is_empty() {
                            let param_env = rustc_middle::ty::ParamEnv::reveal_all();
                            trace!("devirtualize resolving def_id {:?}: {:?}", def_id, def_ty);
                            trace!("substs {:?}", substs);
                            if let Ok(Some(instance)) = rustc_middle::ty::Instance::resolve(
                                self.bv.tcx,
                                param_env,
                                def_id,
                                substs,
                            ) {
                                def_id = instance.def.def_id();
                                trace!("resolved it to {:?}", def_id);
                            }
                        }
                        if self.bv.tcx.is_mir_available(def_id) {
                            self.bv.import_static(Path::new_static(self.bv.tcx, def_id))
                        } else if self.bv.cv.known_names_cache.get(self.bv.tcx, def_id)
                            == KnownNames::AllocRawVecMinNonZeroCap
                        {
                            let param_env = self.bv.tcx.param_env(def_id);
                            if let Ok(ty_and_layout) =
                                self.bv.tcx.layout_of(param_env.and(substs.type_at(0)))
                            {
                                if !ty_and_layout.is_unsized() {
                                    let size_of_t = ty_and_layout.layout.size.bytes();
                                    let min_non_zero_cap: u128 = if size_of_t == 1 {
                                        8
                                    } else if size_of_t <= 1024 {
                                        4
                                    } else {
                                        1
                                    };
                                    return Rc::new((min_non_zero_cap).into());
                                }
                            }
                            Path::new_static(self.bv.tcx, def_id)
                        } else {
                            let cache_key = utils::summary_key_str(self.bv.tcx, def_id);
                            let summary = self
                                .bv
                                .cv
                                .summary_cache
                                .get_persistent_summary_for(&cache_key);
                            if summary.is_computed {
                                let path =
                                    self.bv.import_static(Path::new_static(self.bv.tcx, def_id));
                                self.type_visitor_mut()
                                    .set_path_rustc_type(path.clone(), lty);
                                return self.bv.lookup_path_and_refine_result(path, lty);
                            } else {
                                Path::new_static(self.bv.tcx, def_id)
                            }
                        }
                    }
                };
                self.type_visitor_mut()
                    .set_path_rustc_type(path.clone(), lty);
                let val_at_path = self.bv.lookup_path_and_refine_result(path, lty);
                if let Expression::Variable { .. } = &val_at_path.expression {
                    // Seems like there is nothing at the path, but...
                    if self.bv.tcx.is_mir_available(def_id) {
                        // The MIR body should have computed something. If that something is
                        // a structure, the value of the path will be unknown (only leaf paths have
                        // known values).
                        return val_at_path;
                    }
                    // Seems like a lazily serialized constant. Force evaluation.
                    val = val.eval(self.bv.tcx, self.type_visitor().get_param_env());
                    if let rustc_middle::ty::ConstKind::Unevaluated(..) = &val {
                        // val.eval did not manage to evaluate this, go with unknown.
                        info!(
                            "static def_id with no MIR {:?} {:?}",
                            def_id,
                            utils::summary_key_str(self.bv.tcx, def_id)
                        );
                        info!(
                            "type key {:?}",
                            utils::argument_types_key_str(self.bv.tcx, Some(substs))
                        );
                        return val_at_path;
                    }
                } else {
                    return val_at_path;
                }
            }
        }

        // Don't try to parse serialized functions, just use their types
        // todo: serialized closures and generators do not store enough information in their types.
        match lty.kind() {
            TyKind::Closure(def_id, substs)
            | TyKind::FnDef(def_id, substs)
            | TyKind::Generator(def_id, substs, ..)
            | TyKind::Opaque(def_id, substs) => {
                let specialized_ty = self.type_visitor().specialize_generic_argument_type(
                    lty,
                    &self.type_visitor().generic_argument_map,
                );
                let substs = self
                    .type_visitor()
                    .specialize_substs(substs, &self.type_visitor().generic_argument_map);
                return Rc::new(
                    self.visit_function_reference(*def_id, specialized_ty, Some(substs))
                        .clone()
                        .into(),
                );
            }
            TyKind::FnPtr(..) => {
                //todo: figure out how function pointers are serialized
                debug!("span: {:?}", self.bv.current_span);
                debug!("type kind {:?}", lty.kind());
                debug!("unimplemented constant {:?}", val);
                return Rc::new(ConstantDomain::Unimplemented.into());
            }
            _ => {}
        }

        match &val {
            rustc_middle::ty::ConstKind::Param(ParamConst { index, .. }) => {
                if let Some(gen_args) = self.type_visitor().generic_arguments {
                    if let Some(arg_val) = gen_args.as_ref().get(*index as usize) {
                        return self.visit_const(arg_val.expect_const());
                    }
                }
                assume_unreachable!(
                    "reference to unmatched generic constant argument {:?} {:?}",
                    val,
                    self.bv.current_span
                );
            }
            rustc_middle::ty::ConstKind::Value(ConstValue::ByRef { alloc, offset }) => {
                let alloc_len = alloc.len();
                let offset_bytes = offset.bytes() as usize;
                // The Rust compiler should ensure this.
                assume!(alloc_len > offset_bytes);
                let num_bytes = alloc_len - offset_bytes;
                let bytes =
                    alloc.inspect_with_uninit_and_ptr_outside_interpreter(offset_bytes..alloc_len);
                let heap_val = self.bv.get_new_heap_block(
                    Rc::new((num_bytes as u128).into()),
                    Rc::new(1u128.into()),
                    false,
                    lty,
                );
                let bytes_left_to_deserialize = self.deserialize_constant_bytes(
                    Path::get_as_path(heap_val.clone()),
                    bytes,
                    lty,
                );
                if !bytes_left_to_deserialize.is_empty() {
                    debug!("span: {:?}", self.bv.current_span);
                    debug!("type kind {:?}", lty.kind());
                    debug!("constant value did not serialize correctly {:?}", val);
                }
                return heap_val;
            }
            rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Int(scalar_int))) => {
                let size = scalar_int.size().bytes() as usize;
                let data: u128 = if *scalar_int == ScalarInt::ZST {
                    0
                } else {
                    scalar_int.to_bits(scalar_int.size()).unwrap()
                };
                let byte_array = unsafe { std::mem::transmute::<u128, [u8; 16]>(data) };
                let bytes: &[u8] = &byte_array[0..size];

                match lty.kind() {
                    TyKind::Adt(adt_def, _) if adt_def.is_enum() => {
                        return self.get_enum_variant_as_constant(&val, lty);
                    }
                    TyKind::Adt(..) | TyKind::Tuple(..) => {
                        if *scalar_int == ScalarInt::ZST {
                            return Rc::new(ConstantDomain::Unit.into());
                        }
                        let heap_val = self.bv.get_new_heap_block(
                            Rc::new((size as u128).into()),
                            Rc::new(1u128.into()),
                            false,
                            lty,
                        );
                        let bytes_left_to_deserialize = self.deserialize_constant_bytes(
                            Path::get_as_path(heap_val.clone()),
                            bytes,
                            lty,
                        );
                        if !bytes_left_to_deserialize.is_empty() {
                            debug!("span: {:?}", self.bv.current_span);
                            debug!("type kind {:?}", lty.kind());
                            debug!("constant value did not serialize correctly {:?}", val);
                        }
                        debug!("env {:?}", self.bv.current_environment);
                        return heap_val;
                    }
                    TyKind::Array(elem_type, length) => {
                        let length = self.bv.get_array_length(length);
                        let (array_value, array_path) = self.get_heap_array_and_path(lty, size);
                        self.deserialize_constant_array(array_path, bytes, length, elem_type);
                        return array_value;
                    }
                    _ => {
                        return Rc::new(
                            self.get_constant_from_scalar(lty.kind(), *scalar_int)
                                .clone()
                                .into(),
                        );
                    }
                }
            }
            rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Ptr(ptr))) => {
                match self.bv.tcx.get_global_alloc(ptr.alloc_id) {
                    Some(GlobalAlloc::Memory(alloc)) => {
                        let alloc_len = alloc.len() as u64;
                        let offset_bytes = ptr.offset.bytes();
                        // The Rust compiler should ensure this.
                        assume!(alloc_len > offset_bytes);
                        let size = alloc_len - offset_bytes;
                        let bytes = alloc
                            .get_bytes(
                                &self.bv.tcx,
                                alloc_range(ptr.offset, rustc_target::abi::Size::from_bytes(size)),
                            )
                            .unwrap();
                        match lty.kind() {
                            TyKind::Array(elem_type, length) => {
                                let length = self.bv.get_array_length(length);
                                let (array_value, array_path) =
                                    self.get_heap_array_and_path(lty, size as usize);
                                self.deserialize_constant_array(
                                    array_path, bytes, length, elem_type,
                                );
                                return array_value;
                            }
                            TyKind::Ref(_, t, _) => {
                                if let TyKind::Array(elem_type, length) = t.kind() {
                                    let length = self.bv.get_array_length(length);
                                    let (_, array_path) =
                                        self.get_heap_array_and_path(lty, size as usize);
                                    self.deserialize_constant_array(
                                        array_path.clone(),
                                        bytes,
                                        length,
                                        elem_type,
                                    );
                                    return AbstractValue::make_reference(array_path);
                                }
                            }
                            _ => {}
                        }
                    }
                    Some(GlobalAlloc::Function(_instance)) => {
                        //todo: figure out what kind of constants are encoded this way. Get a test case.
                    }
                    Some(GlobalAlloc::Static(def_id)) => {
                        return AbstractValue::make_reference(
                            self.bv.import_static(Path::new_static(self.bv.tcx, def_id)),
                        );
                    }
                    None => unreachable!("missing allocation {:?}", ptr.alloc_id),
                };
            }
            rustc_middle::ty::ConstKind::Value(ConstValue::Slice { data, start, end }) => {
                assume!(*end > *start); // The Rust compiler should ensure this.
                let size = *end - *start;
                let bytes = data
                    .get_bytes(
                        &self.bv.tcx,
                        alloc_range(
                            rustc_target::abi::Size::from_bytes(*start as u64),
                            rustc_target::abi::Size::from_bytes(size as u64),
                        ),
                    )
                    .unwrap();
                let slice = &bytes[*start..*end];
                match lty.kind() {
                    TyKind::Array(elem_type, length) => {
                        let length = self.bv.get_array_length(length);
                        let (array_value, array_path) = self.get_heap_array_and_path(lty, size);
                        self.deserialize_constant_array(array_path, bytes, length, elem_type);
                        return array_value;
                    }
                    TyKind::Ref(_, t, _) if matches!(t.kind(), TyKind::Slice(..)) => {
                        let elem_type = self.type_visitor().get_element_type(t);
                        let bytes_per_elem = self.type_visitor().get_type_size(elem_type) as usize;
                        let length = size / bytes_per_elem;
                        let (_, array_path) = self.get_heap_array_and_path(t, size);
                        self.deserialize_constant_array(
                            array_path.clone(),
                            bytes,
                            length,
                            elem_type,
                        );
                        return AbstractValue::make_reference(array_path);
                    }
                    TyKind::Ref(_, t, _) if matches!(t.kind(), TyKind::Str) => {
                        let s = std::str::from_utf8(slice).expect("non utf8 str");
                        let string_const = &mut self.bv.cv.constant_value_cache.get_string_for(s);
                        let string_val: Rc<AbstractValue> = Rc::new(string_const.clone().into());
                        let len_val: Rc<AbstractValue> =
                            Rc::new(ConstantDomain::U128(s.len() as u128).into());

                        let str_path = Path::new_computed(string_val.clone());
                        self.bv
                            .current_environment
                            .update_value_at(str_path.clone(), string_val);

                        let len_path = Path::new_length(str_path.clone());
                        self.bv
                            .current_environment
                            .update_value_at(len_path, len_val);
                        return AbstractValue::make_reference(str_path);
                    }
                    _ => {}
                }
            }
            _ => {}
        }

        debug!("span: {:?}", self.bv.current_span);
        debug!("type kind {:?}", lty.kind());
        debug!("unimplemented constant {:?}", val);
        Rc::new(ConstantDomain::Unimplemented.into())
    }

    /// Use a prefix of the byte slice as a serialized value of the given type.
    /// Write the deserialized value to the given path in the current environment.
    /// Return the unused suffix of the byte slice as the result.
    #[logfn_inputs(TRACE)]
    fn deserialize_constant_bytes<'a>(
        &mut self,
        target_path: Rc<Path>,
        bytes: &'a [u8],
        ty: Ty<'tcx>,
    ) -> &'a [u8] {
        self.type_visitor_mut()
            .set_path_rustc_type(target_path.clone(), ty);
        match ty.kind() {
            TyKind::Adt(def, substs) => {
                trace!("deserializing {:?} {:?}", def, substs);
                let mut bytes_left_deserialize = bytes;
                // todo: if there is more than one variant we need to use union fields
                for variant in def.variants.iter() {
                    trace!("deserializing variant {:?}", variant);
                    bytes_left_deserialize = bytes;
                    trace!("bytes_left_deserialize {:?}", bytes_left_deserialize);
                    for (i, field) in variant.fields.iter().enumerate() {
                        trace!("deserializing field({}) {:?}", i, field);
                        let field_path = Path::new_field(target_path.clone(), i);
                        let field_ty = field.ty(self.bv.tcx, substs);
                        bytes_left_deserialize = self.deserialize_constant_bytes(
                            field_path,
                            bytes_left_deserialize,
                            field_ty,
                        );
                    }
                }
                bytes_left_deserialize
            }
            TyKind::Array(elem_type, length) => {
                let length = self.bv.get_array_length(length);
                self.deserialize_constant_array(target_path, bytes, length, elem_type)
            }
            TyKind::Bool => {
                let val = if bytes[0] == 0 {
                    abstract_value::FALSE
                } else {
                    abstract_value::TRUE
                };
                self.bv
                    .current_environment
                    .update_value_at(target_path, Rc::new(val));
                &bytes[1..]
            }
            TyKind::Char => unsafe {
                let ch_ptr = bytes.as_ptr() as *const char;
                let ch = self
                    .bv
                    .cv
                    .constant_value_cache
                    .get_char_for(*ch_ptr)
                    .clone();
                self.bv
                    .current_environment
                    .update_value_at(target_path, Rc::new(ch.into()));
                &bytes[4..]
            },
            TyKind::Int(IntTy::Isize) => unsafe {
                let int_ptr = bytes.as_ptr() as *const isize;
                let i = self.bv.get_i128_const_val((*int_ptr) as i128);
                self.bv.current_environment.update_value_at(target_path, i);
                let size = std::mem::size_of::<isize>();
                &bytes[size..]
            },
            TyKind::Int(IntTy::I8) => unsafe {
                let int_ptr = bytes.as_ptr() as *const i8;
                let i = self.bv.get_i128_const_val((*int_ptr) as i128);
                self.bv.current_environment.update_value_at(target_path, i);
                &bytes[1..]
            },
            TyKind::Int(IntTy::I16) => unsafe {
                let int_ptr = bytes.as_ptr() as *const i16;
                let i = self.bv.get_i128_const_val((*int_ptr) as i128);
                self.bv.current_environment.update_value_at(target_path, i);
                &bytes[2..]
            },
            TyKind::Int(IntTy::I32) => unsafe {
                let int_ptr = bytes.as_ptr() as *const i32;
                let i = self.bv.get_i128_const_val((*int_ptr) as i128);
                self.bv.current_environment.update_value_at(target_path, i);
                &bytes[4..]
            },
            TyKind::Int(IntTy::I64) => unsafe {
                let int_ptr = bytes.as_ptr() as *const i64;
                let i = self.bv.get_i128_const_val((*int_ptr) as i128);
                self.bv.current_environment.update_value_at(target_path, i);
                &bytes[8..]
            },
            TyKind::Int(IntTy::I128) => unsafe {
                let int_ptr = bytes.as_ptr() as *const i128;
                let i = self.bv.get_i128_const_val(*int_ptr);
                self.bv.current_environment.update_value_at(target_path, i);
                &bytes[16..]
            },
            TyKind::Uint(UintTy::Usize) => unsafe {
                let uint_ptr = bytes.as_ptr() as *const usize;
                let u = self.bv.get_u128_const_val((*uint_ptr) as u128);
                self.bv.current_environment.update_value_at(target_path, u);
                let size = std::mem::size_of::<isize>();
                &bytes[size..]
            },
            TyKind::Uint(UintTy::U8) => unsafe {
                let uint_ptr = bytes.as_ptr() as *const u8;
                let u = self.bv.get_u128_const_val((*uint_ptr) as u128);
                self.bv.current_environment.update_value_at(target_path, u);
                &bytes[1..]
            },
            TyKind::Uint(UintTy::U16) => unsafe {
                let uint_ptr = bytes.as_ptr() as *const u16;
                let u = self.bv.get_u128_const_val((*uint_ptr) as u128);
                self.bv.current_environment.update_value_at(target_path, u);
                &bytes[2..]
            },
            TyKind::Uint(UintTy::U32) => unsafe {
                let uint_ptr = bytes.as_ptr() as *const u32;
                let u = self.bv.get_u128_const_val((*uint_ptr) as u128);
                self.bv.current_environment.update_value_at(target_path, u);
                &bytes[4..]
            },
            TyKind::Uint(UintTy::U64) => unsafe {
                let uint_ptr = bytes.as_ptr() as *const u64;
                let u = self.bv.get_u128_const_val((*uint_ptr) as u128);
                self.bv.current_environment.update_value_at(target_path, u);
                &bytes[8..]
            },
            TyKind::Uint(UintTy::U128) => unsafe {
                let uint_ptr = bytes.as_ptr() as *const u128;
                let u = self.bv.get_u128_const_val(*uint_ptr);
                self.bv.current_environment.update_value_at(target_path, u);
                &bytes[16..]
            },
            TyKind::Float(FloatTy::F32) => unsafe {
                let uint_ptr = bytes.as_ptr() as *const u32;
                let f = self
                    .bv
                    .cv
                    .constant_value_cache
                    .get_f32_for(*uint_ptr)
                    .clone();
                self.bv
                    .current_environment
                    .update_value_at(target_path, Rc::new(f.into()));
                &bytes[4..]
            },
            TyKind::Float(FloatTy::F64) => unsafe {
                let uint_ptr = bytes.as_ptr() as *const u64;
                let f = self
                    .bv
                    .cv
                    .constant_value_cache
                    .get_f64_for(*uint_ptr)
                    .clone();
                self.bv
                    .current_environment
                    .update_value_at(target_path, Rc::new(f.into()));
                &bytes[8..]
            },
            TyKind::RawPtr(rustc_middle::ty::TypeAndMut { .. }) | TyKind::Ref(..) => {
                // serialized pointers are not the values pointed to, just some number.
                // todo: figure out how to deference that number and deserialize the
                // value to which this pointer refers.
                self.deserialize_constant_bytes(target_path, bytes, self.bv.tcx.types.usize)
            }
            TyKind::Slice(elem_type) => {
                let elem_size = self.type_visitor().get_type_size(elem_type) as usize;
                checked_assume!(elem_size > 0); // serializing a slice of zero sized elements makes no sense
                let num_elems = bytes.len() / elem_size;
                self.deserialize_constant_array(target_path, bytes, num_elems, elem_type)
            }
            TyKind::Str => {
                let s = std::str::from_utf8(bytes).expect("string should be serialized as utf8");
                let string_const = &mut self.bv.cv.constant_value_cache.get_string_for(s);
                let string_val: Rc<AbstractValue> = Rc::new(string_const.clone().into());
                let len_val: Rc<AbstractValue> =
                    Rc::new(ConstantDomain::U128(s.len() as u128).into());

                let str_path = Path::new_computed(string_val.clone());
                self.bv
                    .current_environment
                    .update_value_at(str_path.clone(), string_val);

                let len_path = Path::new_length(str_path.clone());
                self.bv
                    .current_environment
                    .update_value_at(len_path, len_val);

                self.bv
                    .current_environment
                    .update_value_at(target_path, AbstractValue::make_reference(str_path));
                &[]
            }
            TyKind::Tuple(substs) => {
                let mut bytes_left_deserialize = bytes;
                for (i, subst) in substs.iter().enumerate() {
                    let field_path = Path::new_field(target_path.clone(), i);
                    let field_ty = subst.expect_ty();
                    bytes_left_deserialize = self.deserialize_constant_bytes(
                        field_path,
                        bytes_left_deserialize,
                        field_ty,
                    );
                }
                bytes_left_deserialize
            }
            _ => {
                debug!("Type {:?} is not expected to be serializable", ty.kind());
                self.bv
                    .current_environment
                    .update_value_at(target_path, Rc::new(ConstantDomain::Unimplemented.into()));
                &[]
            }
        }
    }

    /// Allocates a new heap block with length and alignment obtained from the given array
    /// or array slice type.
    #[logfn_inputs(TRACE)]
    fn get_heap_array_and_path(
        &mut self,
        array_type: Ty<'tcx>,
        size_in_bytes: usize,
    ) -> (Rc<AbstractValue>, Rc<Path>) {
        let element_type = self.type_visitor().get_element_type(array_type);
        let (_, elem_alignment) = self
            .type_visitor()
            .get_type_size_and_alignment(element_type);
        let alignment = self.get_u128_const_val(elem_alignment);
        let byte_len_value = self.get_u128_const_val(size_in_bytes as u128);
        let array_value = self
            .bv
            .get_new_heap_block(byte_len_value, alignment, false, array_type);
        let array_path = Path::get_as_path(array_value.clone());
        (array_value, array_path)
    }

    /// Use a prefix of the byte slice as a serialized value of the given array type.
    /// Write the deserialized value to the given path in the current environment.
    /// Return the unused suffix of the byte slice as the result.
    #[logfn_inputs(TRACE)]
    fn deserialize_constant_array<'a>(
        &mut self,
        target_path: Rc<Path>,
        bytes: &'a [u8],
        len: usize,
        elem_ty: Ty<'tcx>,
    ) -> &'a [u8] {
        let mut bytes_left_deserialize = bytes;
        for i in 0..len {
            let elem_path =
                Path::new_index(target_path.clone(), self.get_u128_const_val(i as u128));
            bytes_left_deserialize =
                self.deserialize_constant_bytes(elem_path, bytes_left_deserialize, elem_ty);
        }
        let length_path = Path::new_length(target_path);
        let length_value = self.get_u128_const_val(len as u128);
        self.bv
            .current_environment
            .update_value_at(length_path, length_value);
        bytes_left_deserialize
    }

    /// Used for enum typed constants. The implementation relies closely on the enum layout optimization
    /// in the current implementation of Rust. The enum encoding is not well documented, and it might
    /// subject to changes in future versions of Rust.
    #[logfn_inputs(TRACE)]
    fn get_enum_variant_as_constant(
        &mut self,
        val: &rustc_middle::ty::ConstKind<'tcx>,
        ty: Ty<'tcx>,
    ) -> Rc<AbstractValue> {
        if let rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Int(scalar_int))) = val
        {
            let size = scalar_int.size();
            if size == rustc_target::abi::Size::ZERO {
                return Rc::new(ConstantDomain::U128(0).into());
            }
            let data = scalar_int.to_bits(size).unwrap();
            let param_env = self.type_visitor().get_param_env();
            if let Ok(ty_and_layout) = self.bv.tcx.layout_of(param_env.and(ty)) {
                // The type of the discriminant tag
                let discr_ty = ty_and_layout.ty.discriminant_ty(self.bv.tcx);
                // The layout of the discriminant tag
                let discr_layout = self.bv.tcx.layout_of(param_env.and(discr_ty)).unwrap();

                let discr_signed; // Whether the discriminant tag is signed or not
                let discr_bits; // The actual representation of the discriminant tag
                let discr_index; // The index of the discriminant in the enum definition
                let discr_has_data; // A flag indicating if the enum constant has a sub-component

                match ty_and_layout.variants {
                    Variants::Single { index } => {
                        // The enum only contains one variant.

                        // Truncates the value of the discriminant to fit into the layout.
                        discr_signed = discr_layout.abi.is_signed();
                        discr_bits = match ty_and_layout
                            .ty
                            .discriminant_for_variant(self.bv.tcx, index)
                        {
                            Some(discr) => {
                                if discr_signed {
                                    discr_layout.size.sign_extend(discr.val)
                                } else {
                                    discr_layout.size.truncate(discr.val)
                                }
                            }
                            None => discr_layout.size.truncate(index.as_u32() as u128),
                        };
                        discr_index = index;
                        // A single-variant enum can have niches if and only if this variant has a sub-component
                        // of some special types (such as char).
                        discr_has_data = ty_and_layout.largest_niche.is_some();
                    }
                    Variants::Multiple {
                        ref tag,
                        ref tag_encoding,
                        ref variants,
                        ..
                    } => {
                        // The enum contains multiple (more than one) variants.

                        // The discriminant tag can be defined explicitly, and it can be negative.
                        // Extracts the tag layout that indicates the tag's sign.
                        let tag_layout = self
                            .bv
                            .tcx
                            .layout_of(param_env.and(tag.value.to_int_ty(self.bv.tcx)))
                            .unwrap();
                        discr_signed = tag_layout.abi.is_signed();
                        match *tag_encoding {
                            TagEncoding::Direct => {
                                // Truncates the discriminant value to fit into the layout.
                                // But before the truncation, we have to extend it properly if the tag can be negative.
                                // For example, `std::cmp::Ordering::Less` is defined as -1, and its discriminant
                                // tag is internally represented as u128::MAX in the type definition.
                                // However, the constant literal might have a different memory layout.
                                // Currently, Rust encodes the constant `std::cmp::Ordering::Less` as 0xff.
                                // So we need to first sign_extend 0xff and then truncate to fit into discr_layout.
                                let v = if discr_signed {
                                    tag_layout.size.sign_extend(data)
                                } else {
                                    data
                                };
                                discr_bits = discr_layout.size.truncate(v);

                                // Iterates through all the variant definitions to find the actual index.
                                discr_index = match ty_and_layout.ty.kind() {
                                    TyKind::Adt(adt, _) => adt
                                        .discriminants(self.bv.tcx)
                                        .find(|(_, var)| var.val == discr_bits),
                                    TyKind::Generator(def_id, substs, _) => {
                                        let substs = substs.as_generator();
                                        substs
                                            .discriminants(*def_id, self.bv.tcx)
                                            .find(|(_, var)| var.val == discr_bits)
                                    }
                                    _ => verify_unreachable!(),
                                }
                                .unwrap()
                                .0;

                                discr_has_data = false;
                            }
                            TagEncoding::Niche {
                                dataful_variant,
                                ref niche_variants,
                                niche_start,
                            } => {
                                // A niche means that there are some optimizations in the enum layout.
                                // For example, a value of type Option<char> is encoded as a 32-bit integer.
                                // There exists one single data containing variant (Some(char)).
                                // Other variants are encoded as niches with tag values starting as niche_start.
                                let variants_start = niche_variants.start().as_u32();
                                let variant = if data >= niche_start {
                                    discr_has_data = false;
                                    let variant_index_relative = (data - niche_start) as u32;
                                    let variant_index = variants_start + variant_index_relative;
                                    VariantIdx::from_u32(variant_index)
                                } else {
                                    discr_has_data = true;
                                    let fields = &variants[dataful_variant].fields;
                                    checked_assume!(
                                        fields.count() == 1
                                            && fields.offset(0).bytes() == 0
                                            && fields.memory_index(0) == 0,
                                        "the data containing variant should contain a single sub-component"
                                    );
                                    dataful_variant
                                };
                                discr_bits = discr_layout.size.truncate(variant.as_u32() as u128);
                                discr_index = variant;
                            }
                        }
                    }
                };

                trace!(
                    "discr tag {:?} index {:?} dataful {:?}",
                    discr_bits,
                    discr_index,
                    discr_has_data
                );
                let raw_length = ty_and_layout.size.bytes();
                let raw_alignment = ty_and_layout.align.abi.bytes();
                let e = self.bv.get_new_heap_block(
                    Rc::new((raw_length as u128).into()),
                    Rc::new((raw_alignment as u128).into()),
                    false,
                    ty,
                );
                if let Expression::HeapBlock { .. } = &e.expression {
                    let discr_path = Path::new_discriminant(Path::get_as_path(e.clone()));
                    let discr_data = if discr_signed {
                        self.get_i128_const_val(discr_bits as i128)
                    } else {
                        self.get_u128_const_val(discr_bits)
                    };
                    self.bv
                        .current_environment
                        .update_value_at(discr_path, discr_data);

                    if discr_has_data {
                        use std::ops::Deref;

                        // Obtains the name of this variant.
                        let name_str = {
                            let enum_def = ty.ty_adt_def().unwrap();
                            let variant_def = &enum_def.variants[discr_index];
                            variant_def.ident.name.as_str()
                        };
                        trace!("discr name {:?}", name_str);

                        // Obtains the path to store the data. For example, for Option<char>,
                        // the path should be `(x as Some).0`.
                        let content_path = Path::new_field(
                            Path::new_qualified(
                                Path::get_as_path(e.clone()),
                                Rc::new(PathSelector::Downcast(
                                    Rc::from(name_str.deref()),
                                    discr_index.as_usize(),
                                )),
                            ),
                            0,
                        );
                        let content_data = self.get_u128_const_val(data);
                        self.bv
                            .current_environment
                            .update_value_at(content_path, content_data);
                    }

                    return e;
                }
            } else {
                let e = self.bv.get_new_heap_block(
                    Rc::new(1u128.into()),
                    Rc::new(1u128.into()),
                    false,
                    ty,
                );
                if let Expression::HeapBlock { .. } = &e.expression {
                    let p = Path::new_discriminant(Path::get_as_path(e.clone()));
                    let d = self.get_u128_const_val(data);
                    self.bv.current_environment.update_value_at(p, d);
                    return e;
                }
            }
            verify_unreachable!();
        }
        debug!("span: {:?}", self.bv.current_span);
        debug!("type kind {:?}", ty.kind());
        debug!("unimplemented constant {:?}", val);
        Rc::new(ConstantDomain::Unimplemented.into())
    }

    /// Used only for types with `layout::abi::Scalar` ABI and ZSTs.
    #[logfn_inputs(TRACE)]
    fn get_constant_from_scalar(
        &mut self,
        ty: &TyKind<'tcx>,
        scalar_int: ScalarInt,
    ) -> &ConstantDomain {
        let data = scalar_int.to_bits(scalar_int.size()).unwrap();
        let size = scalar_int.size().bytes();
        match ty {
            TyKind::Bool => {
                if data == 0 {
                    &ConstantDomain::False
                } else {
                    &ConstantDomain::True
                }
            }
            TyKind::Char => &mut self
                .bv
                .cv
                .constant_value_cache
                .get_char_for(char::try_from(data as u32).unwrap()),
            TyKind::Float(..) => match size {
                4 => &mut self.bv.cv.constant_value_cache.get_f32_for(data as u32),
                _ => &mut self.bv.cv.constant_value_cache.get_f64_for(data as u64),
            },
            TyKind::Int(..) => {
                let value: i128 = match size {
                    1 => i128::from(data as i8),
                    2 => i128::from(data as i16),
                    4 => i128::from(data as i32),
                    8 => i128::from(data as i64),
                    _ => data as i128,
                };
                &mut self.bv.cv.constant_value_cache.get_i128_for(value)
            }
            TyKind::Uint(..) => &mut self.bv.cv.constant_value_cache.get_u128_for(data),
            TyKind::RawPtr(..) => &mut self.bv.cv.constant_value_cache.get_u128_for(data),
            _ => assume_unreachable!(),
        }
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
    pub fn visit_function_reference(
        &mut self,
        def_id: DefId,
        ty: Ty<'tcx>,
        generic_args: Option<SubstsRef<'tcx>>,
    ) -> &ConstantDomain {
        //todo: is def_id unique enough? Perhaps add ty?
        if let Some(generic_args) = generic_args {
            self.bv.cv.substs_cache.insert(def_id, generic_args);
        }
        &mut self.bv.cv.constant_value_cache.get_function_constant_for(
            def_id,
            ty,
            generic_args,
            self.bv.tcx,
            &mut self.bv.cv.known_names_cache,
            &mut self.bv.cv.summary_cache,
        )
    }

    /// Returns a normalized Path instance that is the essentially the same as the Place instance, but which
    /// can be serialized and used as a cache key. Also caches the place type with the path as key.
    #[logfn_inputs(TRACE)]
    pub fn visit_rh_place(&mut self, place: &mir::Place<'tcx>) -> Rc<Path> {
        let place_path = self.get_path_for_place(place);
        let mut path = place_path.canonicalize(&self.bv.current_environment);
        let mut ty = self
            .type_visitor()
            .get_path_rustc_type(&path, self.bv.current_span);
        if ty.is_never() {
            ty = self
                .type_visitor()
                .get_rustc_place_type(place, self.bv.current_span);
            debug!("ty {:?}", ty);
        }
        self.type_visitor_mut()
            .set_path_rustc_type(path.clone(), ty);
        match &place_path.value {
            PathEnum::QualifiedPath { selector, .. } if **selector == PathSelector::Deref => {
                if let TyKind::Array(elem_type, _) = &ty.kind() {
                    // The place path dereferences a qualifier and the dereferenced path
                    // canonicalizes to a path to location typed as an array.
                    // This means that the current value of path ended up as the canonicalization of
                    // *&p into p, where p is of type array. The point of all this
                    // aliasing is to get to the first element of the array, so just go there
                    // directly.
                    path = Path::new_index(path, Rc::new(0u128.into()));
                    ty = elem_type;
                    self.type_visitor_mut()
                        .set_path_rustc_type(path.clone(), ty);
                }
            }
            _ => {}
        }
        match &path.value {
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } if **selector == PathSelector::Deref => {
                if let PathEnum::Computed { value } = &qualifier.value {
                    match &value.expression {
                        Expression::Join { left, right, .. } => {
                            let target_type = ExpressionType::from(ty.kind(), self.bv.tcx);
                            let distributed_deref = left
                                .dereference(target_type.clone())
                                .join(right.dereference(target_type), &place_path);
                            path = Path::get_as_path(distributed_deref);
                            self.type_visitor_mut()
                                .set_path_rustc_type(path.clone(), ty);
                        }
                        Expression::WidenedJoin { operand, .. } => {
                            let target_type = ExpressionType::from(ty.kind(), self.bv.tcx);
                            let distributed_deref =
                                operand.dereference(target_type).widen(&place_path);
                            path = Path::get_as_path(distributed_deref);
                            self.type_visitor_mut()
                                .set_path_rustc_type(path.clone(), ty);
                        }
                        _ => (),
                    }
                }
            }
            _ => (),
        };
        path
    }

    /// Returns a Path instance that is essentially the same as the Place instance, but which
    /// can be serialized and used as a cache key. Also caches the place type with the path as key.
    /// The path is not normalized so deref selectors are left in place until it is determined if
    /// the fat pointer is being dereferenced to get at its target value, or dereferenced to make
    /// a copy of it.
    #[logfn_inputs(TRACE)]
    pub fn visit_lh_place(&mut self, place: &mir::Place<'tcx>) -> Rc<Path> {
        self.get_path_for_place(place)
    }

    /// Returns a Path instance that is the essentially the same as the Place instance, but which
    /// can be serialized and used as a cache key.
    #[logfn(TRACE)]
    fn get_path_for_place(&mut self, place: &mir::Place<'tcx>) -> Rc<Path> {
        let ty = self.type_visitor().get_loc_ty(place.local);
        let type_index = self.type_visitor().get_index_for(ty);
        let base_path: Rc<Path> = Path::new_local_parameter_or_result(
            place.local.as_usize(),
            self.bv.mir.arg_count,
            type_index,
        );
        if place.projection.is_empty() {
            match ty.kind() {
                TyKind::Adt(def, ..) => {
                    let ty_name = self.bv.cv.known_names_cache.get(self.bv.tcx, def.did);
                    if ty_name == KnownNames::StdMarkerPhantomData {
                        return Rc::new(PathEnum::PhantomData.into());
                    }
                }
                TyKind::Array(_, len) => {
                    let len_val = self.visit_const(len);
                    let len_path = Path::new_length(base_path.clone());
                    self.bv
                        .current_environment
                        .update_value_at(len_path, len_val);
                }
                TyKind::Closure(def_id, generic_args)
                | TyKind::Generator(def_id, generic_args, ..) => {
                    let func_const = self.visit_function_reference(*def_id, ty, Some(generic_args));
                    let func_val = Rc::new(func_const.clone().into());
                    self.bv
                        .current_environment
                        .update_value_at(base_path.clone(), func_val);
                }
                TyKind::Opaque(def_id, ..) => {
                    //todo: what about generators?
                    if let TyKind::Closure(def_id, generic_args) =
                        self.bv.tcx.type_of(*def_id).kind()
                    {
                        let func_const =
                            self.visit_function_reference(*def_id, ty, Some(generic_args));
                        let func_val = Rc::new(func_const.clone().into());
                        self.bv
                            .current_environment
                            .update_value_at(base_path.clone(), func_val);
                    }
                }
                TyKind::FnDef(def_id, generic_args) => {
                    let func_const = self.visit_function_reference(
                        *def_id,
                        ty,
                        Some(generic_args.as_closure().substs),
                    );
                    let func_val = Rc::new(func_const.clone().into());
                    self.bv
                        .current_environment
                        .update_value_at(base_path.clone(), func_val);
                }
                _ => (),
            }
            base_path
        } else {
            self.visit_projection(base_path, ty, place.projection)
        }
    }

    /// Returns a path that is qualified by the selector corresponding to projection.elem.
    /// If projection has a base, the give base_path is first qualified with the base.
    #[logfn_inputs(TRACE)]
    fn visit_projection(
        &mut self,
        base_path: Rc<Path>,
        base_ty: Ty<'tcx>,
        projection: &[mir::PlaceElem<'tcx>],
    ) -> Rc<Path> {
        let tcx = self.bv.tcx;
        let mut result = base_path;
        let mut ty: Ty<'_> = base_ty;
        for elem in projection.iter() {
            let selector = self.visit_projection_elem(ty, elem);
            match elem {
                mir::ProjectionElem::Deref => {
                    let type_visitor = &mut self.type_visitor_mut();
                    if ty.is_box() {
                        // Deref the pointer at field 0 of the box
                        result = Path::new_field(result, 0);
                        ty = ty.boxed_ty();
                    } else if type_visitor.is_slice_pointer(ty.kind()) {
                        // Deref the thin pointer part
                        ty = type_visitor.get_dereferenced_type(ty);
                        let thin_pointer_path = Path::new_field(result, 0);
                        let deref_path = Path::new_deref(
                            thin_pointer_path,
                            ExpressionType::from(ty.kind(), tcx),
                        );
                        type_visitor.set_path_rustc_type(deref_path.clone(), ty);
                        result = deref_path;
                        continue;
                    } else {
                        ty = type_visitor.get_dereferenced_type(ty);
                    }
                }
                mir::ProjectionElem::Field(_, field_ty) => {
                    ty = self.type_visitor().specialize_generic_argument_type(
                        field_ty,
                        &self.type_visitor().generic_argument_map,
                    );
                    if let TyKind::Adt(def, ..) = ty.kind() {
                        let ty_name = self.bv.cv.known_names_cache.get(tcx, def.did);
                        if ty_name == KnownNames::StdMarkerPhantomData {
                            return Rc::new(PathEnum::PhantomData.into());
                        }
                    }
                    if matches!(selector, PathSelector::Field(0)) {
                        if let TyKind::Adt(def, ..) = base_ty.kind() {
                            debug!("def {:?}", def);
                            if def.repr.transparent() {
                                if let TyKind::Adt(def, ..) = ty.kind() {
                                    if def.repr.transparent() {
                                        debug!("source def {:?}", def);
                                    } else {
                                        // don't add the field access
                                        continue;
                                    }
                                } else {
                                    // don't add the field access
                                    continue;
                                }
                            }
                        }
                    }
                }
                mir::ProjectionElem::Index(..) | mir::ProjectionElem::ConstantIndex { .. } => {
                    ty = self.type_visitor().get_element_type(ty);
                }
                mir::ProjectionElem::Downcast(..) => {
                    ty = self.type_visitor().get_type_for_projection_element(
                        self.bv.current_span,
                        ty,
                        &[*elem],
                    );
                }
                mir::ProjectionElem::Subslice { .. } => {}
            }
            result = Path::new_qualified(result, Rc::new(selector));
        }
        result
    }

    /// Returns a PathSelector instance that is essentially the same as the ProjectionElem instance
    /// but which can be serialized.
    #[logfn_inputs(TRACE)]
    fn visit_projection_elem(
        &mut self,
        base_ty: Ty<'tcx>,
        projection_elem: &mir::ProjectionElem<mir::Local, &rustc_middle::ty::TyS<'tcx>>,
    ) -> PathSelector {
        match projection_elem {
            mir::ProjectionElem::Deref => PathSelector::Deref,
            mir::ProjectionElem::Field(field, ..) => {
                if let TyKind::Adt(def, _) = self
                    .type_visitor()
                    .remove_transparent_wrappers(base_ty)
                    .kind()
                {
                    if def.is_union() {
                        let variants = &def.variants;
                        assume!(variants.len() == 1); // only enums have more than one variant
                        let variant = &variants[variants.last().unwrap()];
                        return PathSelector::UnionField {
                            case_index: field.index(),
                            num_cases: variant.fields.len(),
                        };
                    }
                }
                PathSelector::Field(field.index())
            }
            mir::ProjectionElem::Index(local) => {
                let loc_ty = self.type_visitor().get_loc_ty(*local);
                let type_index = self.type_visitor().get_index_for(loc_ty);
                let local_path = Path::new_local_parameter_or_result(
                    local.as_usize(),
                    self.bv.mir.arg_count,
                    type_index,
                );
                let index_value = self.bv.lookup_path_and_refine_result(local_path, loc_ty);
                PathSelector::Index(index_value)
            }
            mir::ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => PathSelector::ConstantIndex {
                offset: *offset,
                min_length: *min_length,
                from_end: *from_end,
            },
            mir::ProjectionElem::Subslice { from, to, from_end } => PathSelector::ConstantSlice {
                from: *from,
                to: *to,
                from_end: *from_end,
            },
            mir::ProjectionElem::Downcast(name, index) => {
                use std::ops::Deref;
                let name_str = match name {
                    None => Rc::from(format!("variant#{}", index.as_usize())),
                    Some(name) => Rc::from(name.as_str().deref()),
                };
                PathSelector::Downcast(name_str, index.as_usize())
            }
        }
    }
}
