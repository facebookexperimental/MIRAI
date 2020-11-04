// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

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
use crate::smt_solver::SmtResult;
use crate::summaries::{Precondition, Summary};
use crate::tag_domain::Tag;
use crate::utils;
use crate::{abstract_value, type_visitor};

use log_derive::*;
use mirai_annotations::*;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::mir::interpret::{sign_extend, truncate, ConstValue, Scalar};
use rustc_middle::ty::adjustment::PointerCast;
use rustc_middle::ty::layout::PrimitiveExt;
use rustc_middle::ty::subst::SubstsRef;
use rustc_middle::ty::{Const, ParamConst, Ty, TyKind, UserTypeAnnotationIndex};
use rustc_target::abi::{TagEncoding, VariantIdx, Variants};
use std::borrow::Borrow;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::convert::TryInto;
use std::fmt::{Debug, Formatter, Result};
use std::rc::Rc;

/// Holds the state for the basic block visitor
pub struct BlockVisitor<'block, 'analysis, 'compilation, 'tcx, E> {
    pub bv: &'block mut BodyVisitor<'analysis, 'compilation, 'tcx, E>,
}

impl<'block, 'analysis, 'compilation, 'tcx, E> Debug
    for BlockVisitor<'block, 'analysis, 'compilation, 'tcx, E>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "BlockVisitor".fmt(f)
    }
}

/// A visitor that simply traverses enough of the MIR associated with a particular code body
/// so that we can test a call to every default implementation of the MirVisitor trait.
impl<'block, 'analysis, 'compilation, 'tcx, E>
    BlockVisitor<'block, 'analysis, 'compilation, 'tcx, E>
{
    pub fn new(
        body_visitor: &'block mut BodyVisitor<'analysis, 'compilation, 'tcx, E>,
    ) -> BlockVisitor<'block, 'analysis, 'compilation, 'tcx, E> {
        BlockVisitor { bv: body_visitor }
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
            mir::StatementKind::Nop => (),
        }
    }

    /// Write the RHS Rvalue to the LHS Place.
    #[logfn_inputs(TRACE)]
    fn visit_assign(&mut self, place: &mir::Place<'tcx>, rvalue: &mir::Rvalue<'tcx>) {
        let mut path = self.visit_place_defer_refinement(place);
        match &path.value {
            PathEnum::PhantomData => {
                // No need to track this data
                return;
            }
            PathEnum::Alias { .. } | PathEnum::Offset { .. } | PathEnum::QualifiedPath { .. } => {
                path = path.refine_paths(&self.bv.current_environment, 0);
            }
            _ => {}
        }
        self.visit_rvalue(path, rvalue);
    }

    /// Write the discriminant for a variant to the enum Place.
    #[logfn_inputs(TRACE)]
    fn visit_set_discriminant(
        &mut self,
        place: &mir::Place<'tcx>,
        variant_index: rustc_target::abi::VariantIdx,
    ) {
        let target_path = Path::new_discriminant(self.visit_place(place))
            .refine_paths(&self.bv.current_environment, 0);
        let ty = self
            .bv
            .type_visitor
            .get_rustc_place_type(place, self.bv.current_span);
        match ty.kind() {
            TyKind::Adt(..) | TyKind::Generator(..) => {
                let param_env = self.bv.type_visitor.get_param_env();
                if let Ok(ty_and_layout) = self.bv.tcx.layout_of(param_env.and(ty)) {
                    let discr_ty = ty_and_layout.ty.discriminant_ty(self.bv.tcx);
                    let discr_bits = match ty_and_layout
                        .ty
                        .discriminant_for_variant(self.bv.tcx, variant_index)
                    {
                        Some(discr) => discr.val,
                        None => variant_index.as_u32() as u128,
                    };
                    let val = self.get_int_const_val(discr_bits, discr_ty);
                    self.bv
                        .current_environment
                        .update_value_at(target_path, val);
                    return;
                }
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
        let path = Path::new_local_parameter_or_result(local.as_usize(), self.bv.mir.arg_count);
        self.bv
            .current_environment
            .update_value_at(path, abstract_value::BOTTOM.into());
    }

    /// Execute a piece of inline Assembly.
    #[logfn_inputs(TRACE)]
    fn visit_llvm_inline_asm(&mut self, inline_asm: &mir::LlvmInlineAsm<'tcx>) {
        let span = self.bv.current_span;
        let err = self.bv.cv.session.struct_span_warn(
            span,
            "Inline llvm assembly code cannot be analyzed by MIRAI. Unsoundly ignoring this.",
        );
        self.bv.emit_diagnostic(err);
        self.bv.assume_function_is_angelic = true;
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
                values,
                targets,
            } => self.visit_switch_int(discr, switch_ty, values, targets),
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

    /// `discr` evaluates to an integer; jump depending on its value
    /// to one of the targets, and otherwise fallback to last element of `targets`.
    ///
    /// # Arguments
    /// * `discr` - Discriminant value being tested
    /// * `switch_ty` - type of value being tested
    /// * `values` - Possible values. The locations to branch to in each case
    /// are found in the corresponding indices from the `targets` vector.
    /// * `targets` - Possible branch sites. The last element of this vector is used
    /// for the otherwise branch, so targets.len() == values.len() + 1 should hold.
    #[logfn_inputs(TRACE)]
    fn visit_switch_int(
        &mut self,
        discr: &mir::Operand<'tcx>,
        switch_ty: rustc_middle::ty::Ty<'tcx>,
        values: &[u128],
        targets: &[mir::BasicBlock],
    ) {
        assume!(targets.len() == values.len() + 1);
        let mut default_exit_condition = self.bv.current_environment.entry_condition.clone();
        let discr = self.visit_operand(discr);

        // Check if the discriminant is not attached with the tag for constant-time verification.
        if self.bv.check_for_errors {
            if let Some(tag_name) = &self.bv.cv.options.constant_time_tag_name {
                match self.bv.cv.constant_time_tag_cache {
                    None => {
                        // Check if the unknown-constant-time-tag error has been emitted.
                        if !self.bv.cv.constant_time_tag_not_found {
                            self.bv.cv.constant_time_tag_not_found = true;
                            let span = self.bv.current_span;
                            let error = self.bv.cv.session.struct_span_err(
                                span,
                                format!(
                                    "unknown tag type for constant-time verification: {}",
                                    tag_name
                                )
                                .as_str(),
                            );
                            self.bv.emit_diagnostic(error);
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
        for i in 0..values.len() {
            let val = self.get_int_const_val(values[i], switch_ty);
            let cond = discr.equals(val);
            let exit_condition = self
                .bv
                .current_environment
                .entry_condition
                .and(cond.clone());
            let not_cond = cond.logical_not();
            default_exit_condition = default_exit_condition.and(not_cond);
            let target = targets[i];
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
            .insert_mut(targets[values.len()], default_exit_condition);
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
            if self.bv.post_condition.is_none()
                && !self.bv.current_environment.entry_condition.is_top()
            {
                let return_guard = self
                    .bv
                    .current_environment
                    .entry_condition
                    .as_bool_if_known();
                if return_guard.is_none()
                    && !self
                        .bv
                        .current_environment
                        .entry_condition
                        .expression
                        .contains_local_variable()
                {
                    // If no post condition has been explicitly supplied and if the entry condition is interesting
                    // then make the entry condition a post condition, because the function only returns
                    // if this condition is true and thus the caller can assume the condition in its
                    // normal return path.
                    self.bv.post_condition =
                        Some(self.bv.current_environment.entry_condition.clone());
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
        //todo: probably should remove all paths that are rooted in place.

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
            self.bv.type_visitor.generic_argument_map
        );
        trace!("env {:?}", self.bv.current_environment);
        let func_to_call = self.visit_operand(func);
        let func_ref = self.get_func_ref(&func_to_call);
        let func_ref_to_call;
        if let Some(fr) = func_ref {
            func_ref_to_call = fr;
        } else {
            self.report_missing_summary();
            if self.bv.check_for_errors && self.might_be_reachable() {
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
        let callee_generic_arguments = self
            .bv
            .type_visitor
            .specialize_substs(substs, &self.bv.type_visitor.generic_argument_map);
        let actual_args: Vec<(Rc<Path>, Rc<AbstractValue>)> = args
            .iter()
            .map(|arg| (self.get_operand_path(arg), self.visit_operand(arg)))
            .collect();
        let actual_argument_types: Vec<Ty<'tcx>> = args
            .iter()
            .map(|arg| {
                let arg_ty = self.get_operand_rustc_type(arg);
                self.bv.type_visitor.specialize_generic_argument_type(
                    arg_ty,
                    &self.bv.type_visitor.generic_argument_map,
                )
            })
            .collect();
        let callee_generic_argument_map = self.bv.type_visitor.get_generic_arguments_map(
            callee_def_id,
            callee_generic_arguments,
            &actual_argument_types,
        );

        let known_name = func_ref_to_call.known_name;
        let func_const = ConstantDomain::Function(func_ref_to_call);
        let func_const_args = &self.get_function_constant_args(&actual_args);
        let mut call_visitor = CallVisitor::new(
            self,
            callee_def_id,
            Some(callee_generic_arguments),
            callee_generic_argument_map.clone(),
            self.bv.current_environment.clone(),
            func_const,
        );
        call_visitor.actual_args = &actual_args;
        call_visitor.actual_argument_types = &actual_argument_types;
        call_visitor.cleanup = cleanup;
        call_visitor.destination = *destination;
        call_visitor.callee_fun_val = func_to_call;
        call_visitor.function_constant_args = func_const_args;
        trace!("calling func {:?}", call_visitor.callee_func_ref);
        if call_visitor.handled_as_special_function_call() {
            return;
        }
        let function_summary = call_visitor
            .get_function_summary()
            .unwrap_or_else(Summary::default);
        if known_name == KnownNames::StdCloneClone {
            call_visitor.handle_clone(&function_summary);
            return;
        }
        if call_visitor.block_visitor.bv.check_for_errors
            && (!function_summary.is_computed || function_summary.is_angelic)
        {
            call_visitor.deal_with_missing_summary();
        }
        call_visitor.transfer_and_refine_into_current_environment(&function_summary);
    }

    #[logfn_inputs(TRACE)]
    pub fn get_function_constant_args(
        &self,
        actual_args: &[(Rc<Path>, Rc<AbstractValue>)],
    ) -> Vec<(Rc<Path>, Rc<AbstractValue>)> {
        let mut result = vec![];
        for (path, value) in self.bv.current_environment.value_map.iter() {
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
                            | Expression::InitialParameterValue { path: ipath, .. }
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

    /// Give diagnostic, depending on self.bv.options.diag_level
    #[logfn_inputs(TRACE)]
    pub fn report_missing_summary(&mut self) {
        match self.bv.cv.options.diag_level {
            DiagLevel::RELAXED => {
                // Assume the callee is perfect and assume the caller and all of its callers are perfect
                // little angels as well. This cuts down on false positives caused by missing post
                // conditions.
                self.bv.assume_function_is_angelic = true;
            }
            DiagLevel::STRICT => {
                // Assume the callee is perfect and that the caller does not need to prove any
                // preconditions and that the callee guarantees no post conditions.
            }
            DiagLevel::PARANOID => {
                if self.bv.check_for_errors && self.might_be_reachable() {
                    // Give a diagnostic about this call, and make it the programmer's problem.
                    let error = self.bv.cv.session.struct_span_err(
                        self.bv.current_span,
                        "the called function could not be summarized, all bets are off",
                    );
                    self.bv.emit_diagnostic(error);
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
                    .bv
                    .type_visitor
                    .get_path_rustc_type(path, self.bv.current_span);
                let mut specialized_closure_ty =
                    self.bv.type_visitor.specialize_generic_argument_type(
                        closure_ty,
                        &self.bv.type_visitor.generic_argument_map,
                    );
                if let TyKind::Opaque(def_id, substs) = specialized_closure_ty.kind() {
                    self.bv.cv.substs_cache.insert(*def_id, substs);
                    let closure_ty = self.bv.tcx.type_of(*def_id);
                    let map = self
                        .bv
                        .type_visitor
                        .get_generic_arguments_map(*def_id, substs, &[]);
                    specialized_closure_ty = self
                        .bv
                        .type_visitor
                        .specialize_generic_argument_type(closure_ty, &map);
                }
                match specialized_closure_ty.kind() {
                    TyKind::Closure(def_id, substs) | TyKind::FnDef(def_id, substs) => {
                        return extract_func_ref(self.visit_function_reference(
                            *def_id,
                            specialized_closure_ty,
                            substs,
                        ));
                    }
                    //todo: what about generators?
                    TyKind::Ref(_, ty, _) => {
                        let specialized_closure_ty =
                            self.bv.type_visitor.specialize_generic_argument_type(
                                ty,
                                &self.bv.type_visitor.generic_argument_map,
                            );
                        if let TyKind::Closure(def_id, substs) | TyKind::FnDef(def_id, substs) =
                            specialized_closure_ty.kind()
                        {
                            return extract_func_ref(self.visit_function_reference(
                                *def_id,
                                specialized_closure_ty,
                                substs,
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
        let param_env = self.bv.type_visitor.get_param_env();
        let is_signed;
        if let Ok(ty_and_layout) = self.bv.tcx.layout_of(param_env.and(ty)) {
            is_signed = ty_and_layout.abi.is_signed();
            let size = ty_and_layout.size;
            if is_signed {
                val = sign_extend(val, size);
            } else {
                val = truncate(val, size);
            }
        } else {
            is_signed = ty.is_signed();
        }
        if is_signed {
            self.get_i128_const_val(val as i128)
        } else {
            self.get_u128_const_val(val)
        }
    }

    /// Emit a diagnostic to the effect that the current call might violate a the given precondition
    /// of the called function. Use the provenance and spans of the precondition to point out related locations.
    #[logfn_inputs(TRACE)]
    pub fn emit_diagnostic_for_precondition(&mut self, precondition: &Precondition, warn: bool) {
        precondition!(self.bv.check_for_errors);
        // In relaxed mode we don't want to complain if the condition or reachability depends on
        // a parameter, since it is assumed that an implicit precondition was intended by the author.
        if matches!(self.bv.cv.options.diag_level, DiagLevel::RELAXED)
            && (precondition.condition.expression.contains_parameter()
                || self
                    .bv
                    .current_environment
                    .entry_condition
                    .expression
                    .contains_parameter())
        {
            return;
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
        let mut err = self
            .bv
            .cv
            .session
            .struct_span_warn(span, diagnostic.as_ref());
        for pc_span in precondition.spans.iter() {
            let span_str = self.bv.tcx.sess.source_map().span_to_string(*pc_span);
            if span_str.starts_with("/rustc/") {
                err.span_note(*pc_span, &format!("related location {}", span_str));
            } else {
                err.span_note(*pc_span, "related location");
            };
        }
        self.bv.emit_diagnostic(err);
    }

    /// Extend the current post condition by the given `cond`. If none was set before,
    /// this will just set it for the first time. If there is already a post condition.
    /// we check whether it is safe to extend it. It is considered safe if the block where
    /// it was set dominates the existing one.
    #[logfn_inputs(TRACE)]
    pub fn try_extend_post_condition(&mut self, cond: &Rc<AbstractValue>) {
        precondition!(self.bv.check_for_errors);
        if cond.expression.contains_local_variable() {
            // The caller won't have a use for this
            return;
        }
        let this_block = self.bv.current_location.block;
        match (self.bv.post_condition.clone(), self.bv.post_condition_block) {
            (Some(last_cond), Some(last_block)) => {
                let dominators = self.bv.mir.dominators();
                if dominators.is_dominated_by(this_block, last_block) {
                    // We can extend the last condition as all paths to this condition
                    // lead over it
                    self.bv.post_condition = Some(last_cond.and(cond.clone()));
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
                self.bv.post_condition = Some(cond.clone());
                self.bv.post_condition_block = Some(this_block);
            }
        }
    }

    /// Check if the given condition is reachable and true.
    /// If not issue a warning if the function is public and return the warning message, if
    /// the condition is not a post condition.
    #[logfn_inputs(TRACE)]
    pub fn check_condition(
        &mut self,
        cond: &Rc<AbstractValue>,
        message: &str,
        is_post_condition: bool,
    ) -> Option<Rc<str>> {
        precondition!(self.bv.check_for_errors);
        if cond.is_bottom() {
            return None;
        }
        let (cond_as_bool, entry_cond_as_bool) =
            self.bv.check_condition_value_and_reachability(cond);

        // If we never get here, rather call verify_unreachable!()
        if !entry_cond_as_bool.unwrap_or(true) {
            let span = self.bv.current_span;
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

        // If the condition is always false, give an error since that is bad style.
        if !cond_as_bool.unwrap_or(true) {
            // If the condition is always false, give a style error
            let span = self.bv.current_span;
            let error = self
                .bv
                .cv
                .session
                .struct_span_err(span, "provably false verification condition");
            self.bv.emit_diagnostic(error);
            if !is_post_condition
                && entry_cond_as_bool.is_none()
                && self.bv.preconditions.len() < k_limits::MAX_INFERRED_PRECONDITIONS
            {
                // promote the path as a precondition. I.e. the program is only correct,
                // albeit badly written, if we never get here.
                let condition = self.bv.current_environment.entry_condition.logical_not();
                if !condition.expression.contains_local_variable() {
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
        if self.bv.function_being_analyzed_is_root()
            || cond.expression.contains_local_variable()
            || self.bv.preconditions.len() >= k_limits::MAX_INFERRED_PRECONDITIONS
        {
            // In relaxed mode we don't want to complain if the condition or reachability depends on
            // a parameter, since it is assumed that an implicit precondition was intended by the author.
            if matches!(self.bv.cv.options.diag_level, DiagLevel::RELAXED)
                && (cond.expression.contains_parameter()
                    || self
                        .bv
                        .current_environment
                        .entry_condition
                        .expression
                        .contains_parameter())
            {
                return None;
            }
            // We expect public functions to have programmer supplied preconditions
            // that preclude any assertions from failing. So, at this stage we get to
            // complain a bit.
            let span = self.bv.current_span;
            let warning = self.bv.cv.session.struct_span_warn(span, warning.as_str());
            self.bv.emit_diagnostic(warning);
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
            match tag_check_as_bool {
                None => {
                    // We cannot decide the result of the tag check.
                    // In this case, report a warning if we don't know all of the callers, we
                    // reach a k-limit, or the tag check contains a local variable so that we
                    // cannot promote it later as a precondition.
                    if self.bv.function_being_analyzed_is_root()
                        || self.bv.preconditions.len() >= k_limits::MAX_INFERRED_PRECONDITIONS
                    {
                        let span = self.bv.current_span;
                        let warning = self.bv.cv.session.struct_span_warn(
                            span,
                            format!("the {} may have a {} tag", value_name, tag_name).as_str(),
                        );
                        self.bv.emit_diagnostic(warning);
                    } else if tag_check.expression.contains_local_variable() {
                        let span = self.bv.current_span;
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
                    let span = self.bv.current_span;
                    let error = self.bv.cv.session.struct_span_err(
                        span,
                        format!("the {} has a {} tag", value_name, tag_name).as_str(),
                    );
                    self.bv.emit_diagnostic(error);
                }

                _ => {}
            }

            // We promote the tag check as a precondition if it is not always true, it does not
            // contain local variables, and we don't reach a k-limit.
            if !tag_check_as_bool.unwrap_or(false)
                && !tag_check.expression.contains_local_variable()
                && self.bv.preconditions.len() < k_limits::MAX_INFERRED_PRECONDITIONS
            {
                let condition = self
                    .bv
                    .current_environment
                    .entry_condition
                    .logical_not()
                    .or(tag_check);
                let precondition = Precondition {
                    condition,
                    message: Rc::from(format!("the {} may have a {} tag", value_name, tag_name)),
                    provenance: None,
                    spans: vec![self.bv.current_span],
                };
                self.bv.preconditions.push(precondition);
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
                            let error = self.bv.cv.session.struct_span_warn(span, error);
                            self.bv.emit_diagnostic(error);
                            // No need to push a precondition, the caller can never satisfy it.
                            return;
                        }
                    }

                    // At this point, we don't know that this assert is unreachable and we don't know
                    // that the condition is as expected, so we need to warn about it somewhere.
                    if self.bv.function_being_analyzed_is_root()
                        || self.bv.preconditions.len() >= k_limits::MAX_INFERRED_PRECONDITIONS
                        || cond_val.expression.contains_local_variable()
                    {
                        // In relaxed mode we don't want to complain if the condition or reachability depends on
                        // a parameter, since it is assumed that an implicit precondition was intended by the author.
                        if matches!(self.bv.cv.options.diag_level, DiagLevel::RELAXED)
                            && (cond_val.expression.contains_parameter()
                                || self
                                    .bv
                                    .current_environment
                                    .entry_condition
                                    .expression
                                    .contains_parameter())
                        {
                            return;
                        }
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
                    if !cond_val.expression.contains_local_variable()
                        && self.bv.preconditions.len() < k_limits::MAX_INFERRED_PRECONDITIONS
                    {
                        let expected_cond = if expected {
                            cond_val
                        } else {
                            cond_val.logical_not()
                        };
                        // To make sure that this assertion never fails, we should either never
                        // get here (!entry_condition) or expected_cond should be true.
                        let condition = self
                            .bv
                            .current_environment
                            .entry_condition
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
    pub fn might_be_reachable(&mut self) -> bool {
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
            let smt_expr = {
                let ec = &self.bv.current_environment.entry_condition.expression;
                self.bv.smt_solver.get_as_smt_predicate(ec)
            };
            self.bv.smt_solver.set_backtrack_position();
            self.bv.smt_solver.assert(&smt_expr);
            if self.bv.smt_solver.solve() == SmtResult::Unsatisfiable {
                // The solver can prove that the entry condition is always false.
                entry_cond_as_bool = Some(false);
            }
            self.bv.smt_solver.backtrack();
        }
        entry_cond_as_bool.unwrap_or(true)
    }

    /// Execute a piece of inline Assembly.
    #[logfn_inputs(TRACE)]
    fn visit_inline_asm(&mut self, target: &Option<mir::BasicBlock>) {
        let span = self.bv.current_span;
        let diagnostic = self.bv.cv.session.struct_span_warn(
            span,
            "Inline assembly code cannot be analyzed by MIRAI. Unsoundly ignoring this.",
        );
        self.bv.emit_diagnostic(diagnostic);
        self.bv.assume_function_is_angelic = true;
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
                self.visit_repeat(path, operand, *count);
            }
            mir::Rvalue::Ref(_, _, place) | mir::Rvalue::AddressOf(_, place) => {
                self.visit_address_of(path, place);
            }
            mir::Rvalue::ThreadLocalRef(def_id) => {
                self.visit_thread_local_ref(*def_id);
            }
            mir::Rvalue::Len(place) => {
                self.visit_len(path, place);
            }
            mir::Rvalue::Cast(cast_kind, operand, ty) => {
                let specialized_ty = self.bv.type_visitor.specialize_generic_argument_type(
                    ty,
                    &self.bv.type_visitor.generic_argument_map,
                );
                self.visit_cast(path, *cast_kind, operand, specialized_ty);
            }
            mir::Rvalue::BinaryOp(bin_op, left_operand, right_operand) => {
                self.visit_binary_op(path, *bin_op, left_operand, right_operand);
            }
            mir::Rvalue::CheckedBinaryOp(bin_op, left_operand, right_operand) => {
                self.visit_checked_binary_op(path, *bin_op, left_operand, right_operand);
            }
            mir::Rvalue::NullaryOp(null_op, ty) => {
                let specialized_ty = self.bv.type_visitor.specialize_generic_argument_type(
                    ty,
                    &self.bv.type_visitor.generic_argument_map,
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
                let mir::Constant {
                    user_ty, literal, ..
                } = constant.borrow();
                let rh_type = literal.ty;
                let const_value = self.visit_constant(*user_ty, &literal);
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
                        let rpath = Path::new_alias(const_value.clone());
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
        let rpath = self.visit_place(place);
        let rtype = self
            .bv
            .type_visitor
            .get_rustc_place_type(place, self.bv.current_span);
        self.bv
            .copy_or_move_elements(target_path, rpath, rtype, false);
    }

    /// For each (path', value) pair in the environment where path' is rooted in place,
    /// add a (path'', value) pair to the environment where path'' is a copy of path re-rooted
    /// with place, and also remove the (path', value) pair from the environment.
    #[logfn_inputs(TRACE)]
    fn visit_used_move(&mut self, target_path: Rc<Path>, place: &mir::Place<'tcx>) {
        let rpath = self.visit_place(place);
        let rtype = self
            .bv
            .type_visitor
            .get_rustc_place_type(place, self.bv.current_span);
        self.bv
            .copy_or_move_elements(target_path, rpath, rtype, true);
    }

    /// path = [x; 32]
    #[logfn_inputs(TRACE)]
    fn visit_repeat(&mut self, path: Rc<Path>, operand: &mir::Operand<'tcx>, count: &Const<'tcx>) {
        let length_path = Path::new_length(path.clone());
        let length_value = self.visit_constant(None, count);
        self.bv
            .current_environment
            .update_value_at(length_path, length_value.clone());
        let slice_path =
            Path::new_slice(path, length_value).refine_paths(&self.bv.current_environment, 0);
        let initial_value = self.visit_operand(operand);
        self.bv
            .current_environment
            .update_value_at(slice_path, initial_value);
    }

    /// path = &x or &mut x or &raw const x
    #[logfn_inputs(TRACE)]
    fn visit_address_of(&mut self, path: Rc<Path>, place: &mir::Place<'tcx>) {
        let target_type = self
            .bv
            .type_visitor
            .get_path_rustc_type(&path, self.bv.current_span);
        let value_path = self.visit_place_defer_refinement(place);
        let value = match &value_path.value {
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } if *selector.as_ref() == PathSelector::Deref => {
                // We are taking a reference to the result of a deref. This is a bit awkward.
                // The deref, by itself, essentially does a copy of the value denoted by the qualifier.
                // When combined with an address_of operation, however, things are more complicated.
                // If the contents at offset 0 from the target of the pointer being dereferenced is
                // a fat (slice) pointer then the address_of operation results in a copy of the fat pointer.
                // We check for this by looking at the type of the operation result target.
                if type_visitor::is_slice_pointer(target_type.kind())
                    || self
                        .bv
                        .type_visitor
                        .starts_with_slice_pointer(target_type.kind())
                {
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
                                qualifier.refine_paths(&self.bv.current_environment, 0),
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
                    self.bv.copy_or_move_elements(
                        path,
                        qualifier.refine_paths(&self.bv.current_environment, 0),
                        target_type,
                        false,
                    );
                    return;
                } else {
                    // If the target is not a fat pointer, it must be a thin pointer since an
                    // address of operator can hardly result in anything else. So, in this case,
                    // &*source_thin_ptr should just be a non canonical alias for source_thin_ptr.
                    self.bv.copy_or_move_elements(
                        path,
                        qualifier.refine_paths(&self.bv.current_environment, 0),
                        target_type,
                        false,
                    );
                    return;
                }
            }
            PathEnum::Alias { .. } | PathEnum::Offset { .. } | PathEnum::QualifiedPath { .. } => {
                AbstractValue::make_reference(
                    value_path.refine_paths(&self.bv.current_environment, 0),
                )
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
    fn visit_thread_local_ref(&mut self, def_id: DefId) -> Rc<AbstractValue> {
        let static_var = Path::new_static(self.bv.tcx, def_id);
        AbstractValue::make_reference(static_var)
    }

    /// path = length of a [X] or [X;n] value.
    #[logfn_inputs(TRACE)]
    fn visit_len(&mut self, path: Rc<Path>, place: &mir::Place<'tcx>) {
        let place_ty = self
            .bv
            .type_visitor
            .get_rustc_place_type(place, self.bv.current_span);
        let len_value = if let TyKind::Array(_, len) = place_ty.kind() {
            // We only get here if "-Z mir-opt-level=0" was specified.
            // With more optimization the len instruction becomes a constant.
            self.visit_constant(None, &len)
        } else {
            let mut value_path = self.visit_place_defer_refinement(place);
            if let PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } = &value_path.value
            {
                if let PathSelector::Deref = selector.as_ref() {
                    let qualifier_type = self
                        .bv
                        .type_visitor
                        .get_path_rustc_type(qualifier, self.bv.current_span);
                    if type_visitor::is_slice_pointer(qualifier_type.kind()) {
                        // de-referencing a slice pointer is normally the same as de-referencing its
                        // thin pointer, so self.visit_place above assumed that much.
                        // In this context, however, we want the length of the slice pointer,
                        // so we need to drop the thin pointer field selector.
                        if let PathEnum::QualifiedPath {
                            qualifier,
                            selector,
                            ..
                        } = &qualifier.value
                        {
                            checked_assume!(matches!(selector.as_ref(), PathSelector::Field(0)));
                            value_path = qualifier.clone();
                        } else {
                            assume_unreachable!("deref of a slice pointer did not produce ptr.0");
                        }
                    }
                } else {
                    assume_unreachable!("{:?}", selector);
                }
            }
            let length_path =
                Path::new_length(value_path).refine_paths(&self.bv.current_environment, 0);
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
                let source_path = self.visit_place(place);
                let source_type = self.get_operand_rustc_type(operand);
                if let PointerCast::Unsize = pointer_cast {
                    // Unsize a pointer/reference value, e.g., `&[T; n]` to`&[T]`.
                    // If the resulting type is a fat pointer, we might have to upgrade the pointer.
                    if self.bv.type_visitor.starts_with_slice_pointer(ty.kind()) {
                        // Note that the source could be a thin or fat pointer.
                        if !self
                            .bv
                            .type_visitor
                            .starts_with_slice_pointer(source_type.kind())
                        {
                            // Need to upgrade the thin pointer to a fat pointer
                            let target_thin_pointer_path =
                                Path::get_path_to_thin_pointer_at_offset_0(
                                    self.bv.tcx,
                                    &self.bv.current_environment,
                                    &path,
                                    ty,
                                )
                                .expect("there to be such path because ty starts with it");
                            let source_thin_pointer_path =
                                Path::get_path_to_thin_pointer_at_offset_0(
                                    self.bv.tcx,
                                    &self.bv.current_environment,
                                    &source_path,
                                    source_type,
                                )
                                .expect(
                                    "there to be such a path because source_type can cast to target type",
                                );
                            let thin_ptr_type = self.bv.type_visitor.get_path_rustc_type(
                                &source_thin_pointer_path,
                                self.bv.current_span,
                            );
                            let target_type = type_visitor::get_target_type(thin_ptr_type);
                            self.bv.copy_or_move_elements(
                                target_thin_pointer_path.clone(),
                                source_thin_pointer_path.clone(),
                                thin_ptr_type,
                                is_move,
                            );
                            let len_selector = Rc::new(PathSelector::Field(1));
                            let len_value = if let TyKind::Array(_, len) = target_type.kind() {
                                // We only get here if "-Z mir-opt-level=0" was specified.
                                // With more optimization the len instruction becomes a constant.
                                self.visit_constant(None, &len)
                            } else {
                                let len_source_path =
                                    source_thin_pointer_path.replace_selector(len_selector.clone());
                                self.bv.lookup_path_and_refine_result(
                                    len_source_path,
                                    self.bv.tcx.types.usize,
                                )
                            };
                            let len_target_path =
                                target_thin_pointer_path.replace_selector(len_selector);
                            self.bv
                                .current_environment
                                .update_value_at(len_target_path, len_value);
                            return;
                        }
                    }
                }
                self.bv
                    .copy_or_move_elements(path, source_path, ty, is_move);
            }
            mir::CastKind::Misc => {
                let result = self
                    .visit_operand(operand)
                    .cast(ExpressionType::from(ty.kind()));
                if let mir::Operand::Move(place) = operand {
                    let source_path = self.visit_place(place);
                    self.bv.current_environment.value_map =
                        self.bv.current_environment.value_map.remove(&source_path);
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
                    .bv
                    .type_visitor
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
            .bv
            .type_visitor
            .get_first_part_of_target_path_type_tuple(&path, self.bv.current_span);
        let left = self.visit_operand(left_operand);
        let right = self.visit_operand(right_operand);
        let (result, overflow_flag) = Self::do_checked_binary_op(bin_op, target_type, left, right);
        let path0 = Path::new_field(path.clone(), 0).refine_paths(&self.bv.current_environment, 0);
        self.bv.current_environment.update_value_at(path0, result);
        let path1 = Path::new_field(path, 1).refine_paths(&self.bv.current_environment, 0);
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
        let param_env = self.bv.type_visitor.get_param_env();
        let len = if let Ok(ty_and_layout) = self.bv.tcx.layout_of(param_env.and(ty)) {
            Rc::new((ty_and_layout.layout.size.bytes() as u128).into())
        } else {
            //todo: need an expression that eventually refines into the actual layout size
            AbstractValue::make_typed_unknown(ExpressionType::U128, Path::new_local(998))
        };
        let alignment = Rc::new(1u128.into());
        let value = match null_op {
            mir::NullOp::Box => {
                // The box is a struct that is located at path.
                // It contains a pointer at field 0, which is a struct of type Unique,
                // which contains the pointer that points to the new heap block.
                path = Path::new_field(Path::new_field(path, 0), 0);
                self.bv.get_new_heap_block(len, alignment, false, ty)
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
                    .bv
                    .type_visitor
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
        let discriminant_path = Path::new_discriminant(self.visit_place(place));
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
            let index_path = Path::new_index(path.clone(), index_value)
                .refine_paths(&self.bv.current_environment, 0);
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
                let mir::Constant {
                    user_ty, literal, ..
                } = constant.borrow();
                let const_value = self.visit_constant(*user_ty, &literal);
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
            mir::Operand::Copy(place) | mir::Operand::Move(place) => self.visit_place(place),
            mir::Operand::Constant(..) => Path::new_alias(self.visit_operand(operand)),
        }
    }

    /// Returns the rustc Ty of the given operand.
    #[logfn_inputs(TRACE)]
    fn get_operand_rustc_type(&mut self, operand: &mir::Operand<'tcx>) -> Ty<'tcx> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => self
                .bv
                .type_visitor
                .get_rustc_place_type(place, self.bv.current_span),
            mir::Operand::Constant(constant) => {
                let mir::Constant { literal, .. } = constant.borrow();
                literal.ty
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
                let mir::Constant {
                    user_ty, literal, ..
                } = constant.borrow();
                self.visit_constant(*user_ty, &literal)
            }
        }
    }

    /// Copy: The value must be available for use afterwards.
    ///
    /// This implies that the type of the place must be `Copy`; this is true
    /// by construction during build, but also checked by the MIR type checker.
    #[logfn_inputs(TRACE)]
    fn visit_copy(&mut self, place: &mir::Place<'tcx>) -> Rc<AbstractValue> {
        let path = self.visit_place(place);
        let rust_place_type = self
            .bv
            .type_visitor
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
        let path = self.visit_place(place);
        let rust_place_type = self
            .bv
            .type_visitor
            .get_rustc_place_type(place, self.bv.current_span);
        self.bv.lookup_path_and_refine_result(path, rust_place_type)
    }

    /// Synthesizes a constant value. Also used for static variable values.
    #[logfn_inputs(TRACE)]
    pub fn visit_constant(
        &mut self,
        user_ty: Option<UserTypeAnnotationIndex>,
        literal: &Const<'tcx>,
    ) -> Rc<AbstractValue> {
        let mut val = literal.val;
        let ty = literal.ty;
        if let rustc_middle::ty::ConstKind::Unevaluated(def_ty, substs, promoted) = &literal.val {
            if def_ty.const_param_did.is_some() {
                val = val.eval(self.bv.tcx, self.bv.type_visitor.get_param_env());
            } else {
                let def_id = def_ty.def_id_for_type_of();
                let substs = self
                    .bv
                    .type_visitor
                    .specialize_substs(substs, &self.bv.type_visitor.generic_argument_map);
                self.bv.cv.substs_cache.insert(def_id, substs);
                let path = match promoted {
                    Some(promoted) => {
                        let index = promoted.index();
                        Rc::new(PathEnum::PromotedConstant { ordinal: index }.into())
                    }
                    None => Path::new_static(self.bv.tcx, def_id),
                };
                self.bv.type_visitor.path_ty_cache.insert(path.clone(), ty);
                // Note that this might not find the promoted constant in the current environment,
                // even though it was imported at the beginning of visit_body. This happens
                // when the current environment starts of empty because we are visiting an
                // unreachable block for error reporting purposes.
                //todo: keep track of the first state containing the promoted constants and use that
                // to lookup PromotedConstant paths.
                let val_at_path = self.bv.lookup_path_and_refine_result(path, ty);
                if let Expression::Variable { .. } = &val_at_path.expression {
                    // Seems like there is nothing at the path, but...
                    if self.bv.tcx.is_mir_available(def_id) {
                        // The MIR body should have computed something. If that something is
                        // a structure, the value of the path will be unknown (only leaf paths have
                        // known values). Alternatively, this could be a simple value that is not
                        // in the environment as explained in the Note above.
                        return val_at_path;
                    }
                    // Seems like a lazily serialized constant. Force evaluation.
                    val = val.eval(self.bv.tcx, self.bv.type_visitor.get_param_env());
                    if let rustc_middle::ty::ConstKind::Unevaluated(..) = &val {
                        // val.eval did not manage to evaluate this, go with unknown.
                        return val_at_path;
                    }
                } else {
                    return val_at_path;
                }
            }
        }

        let result;
        match ty.kind() {
            TyKind::Bool
            | TyKind::Char
            | TyKind::Float(..)
            | TyKind::Int(..)
            | TyKind::Uint(..) => match &val {
                rustc_middle::ty::ConstKind::Param(ParamConst { index, .. }) => {
                    if let Some(gen_args) = self.bv.type_visitor.generic_arguments {
                        if let Some(arg_val) = gen_args.as_ref().get(*index as usize) {
                            return self.visit_constant(None, arg_val.expect_const());
                        }
                    } else {
                        // todo: figure out why gen_args is None for generic types when
                        // the flag MIRAI_START_FRESH is on.
                        return abstract_value::BOTTOM.into();
                    }
                    assume_unreachable!(
                        "reference to unmatched generic constant argument {:?} {:?}",
                        literal,
                        self.bv.current_span
                    );
                }
                rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Raw {
                    data,
                    size,
                })) => {
                    result = self.get_constant_from_scalar(&ty.kind(), *data, *size);
                }
                _ => {
                    assume_unreachable!(
                        "unexpected kind of literal {:?} {:?}",
                        literal,
                        self.bv.current_span
                    );
                }
            },
            TyKind::FnDef(def_id, substs)
            | TyKind::Closure(def_id, substs)
            | TyKind::Generator(def_id, substs, ..) => {
                let specialized_ty = self.bv.type_visitor.specialize_generic_argument_type(
                    ty,
                    &self.bv.type_visitor.generic_argument_map,
                );
                let substs = self
                    .bv
                    .type_visitor
                    .specialize_substs(substs, &self.bv.type_visitor.generic_argument_map);
                result = self.visit_function_reference(*def_id, specialized_ty, substs);
            }
            TyKind::Ref(_, t, _) if matches!(t.kind(), TyKind::Str) => {
                if let rustc_middle::ty::ConstKind::Value(ConstValue::Slice { data, start, end }) =
                    &val
                {
                    return self.get_reference_to_slice(ty.kind(), data, *start, *end);
                } else {
                    debug!("unsupported val of type Ref: {:?}", literal);
                    unimplemented!();
                };
            }
            TyKind::Ref(_, t, _) if matches!(t.kind(), TyKind::Array(..)) => {
                if let TyKind::Array(elem_type, length) = *t.kind() {
                    return self
                        .visit_reference_to_array_constant(&val, literal.ty, elem_type, length);
                } else {
                    unreachable!(); // match guard
                }
            }
            TyKind::Ref(_, t, _) if matches!(t.kind(), TyKind::Slice(..)) => match &val {
                rustc_middle::ty::ConstKind::Value(ConstValue::Slice { data, start, end }) => {
                    // The rust compiler should ensure this.
                    assume!(*end >= *start);
                    let slice_len = *end - *start;
                    let bytes = data
                        .get_bytes(
                            &self.bv.tcx,
                            // invent a pointer, only the offset is relevant anyway
                            mir::interpret::Pointer::new(
                                mir::interpret::AllocId(0),
                                rustc_target::abi::Size::from_bytes(*start as u64),
                            ),
                            rustc_target::abi::Size::from_bytes(slice_len as u64),
                        )
                        .unwrap();

                    let slice = &bytes[*start..*end];
                    let e_type = if let TyKind::Slice(elem_type) = t.kind() {
                        ExpressionType::from(elem_type.kind())
                    } else {
                        unreachable!()
                    };
                    return self.deconstruct_reference_to_constant_array(
                        slice,
                        e_type,
                        None,
                        type_visitor::get_target_type(ty),
                    );
                }
                _ => {
                    debug!("unsupported val of type Ref: {:?}", literal);
                    unimplemented!();
                }
            },
            TyKind::RawPtr(rustc_middle::ty::TypeAndMut {
                ty,
                mutbl: rustc_hir::Mutability::Mut,
            })
            | TyKind::Ref(_, ty, rustc_hir::Mutability::Mut) => match &val {
                rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Ptr(p))) => {
                    let summary_cache_key = format!("{:?}", p).into();
                    let expression_type: ExpressionType = ExpressionType::from(ty.kind());
                    let path = Rc::new(
                        PathEnum::StaticVariable {
                            def_id: None,
                            summary_cache_key,
                            expression_type,
                        }
                        .into(),
                    );
                    return self.bv.lookup_path_and_refine_result(path, ty);
                }
                _ => assume_unreachable!(),
            },
            TyKind::Ref(_, ty, rustc_hir::Mutability::Not) => {
                return self.get_reference_to_constant(&val, ty);
            }
            TyKind::Adt(adt_def, _) if adt_def.is_enum() => {
                return self.get_enum_variant_as_constant(&val, ty);
            }
            TyKind::Tuple(..) | TyKind::Adt(..) => {
                match &val {
                    rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Raw {
                        size: 0,
                        ..
                    })) => {
                        return self.bv.get_new_heap_block(
                            Rc::new(0u128.into()),
                            Rc::new(1u128.into()),
                            false,
                            ty,
                        );
                    }
                    rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Raw {
                        data,
                        size,
                    })) => {
                        let heap_val = self.bv.get_new_heap_block(
                            Rc::new((*size as u128).into()),
                            Rc::new(1u128.into()),
                            false,
                            ty,
                        );
                        let path_to_scalar = Path::get_path_to_field_at_offset_0(
                            self.bv.tcx,
                            &self.bv.current_environment,
                            &Path::get_as_path(heap_val.clone()),
                            ty,
                        )
                        .unwrap_or_else(|| {
                            unrecoverable!(
                                "expected serialized constant to be correct at {:?}",
                                self.bv.current_span
                            )
                        });
                        let scalar_ty = self
                            .bv
                            .type_visitor
                            .get_path_rustc_type(&path_to_scalar, self.bv.current_span);
                        let scalar_val: Rc<AbstractValue> = Rc::new(
                            self.get_constant_from_scalar(&scalar_ty.kind(), *data, *size)
                                .clone()
                                .into(),
                        );
                        self.bv
                            .current_environment
                            .update_value_at(path_to_scalar, scalar_val);
                        return heap_val;
                    }
                    _ => {
                        debug!("span: {:?}", self.bv.current_span);
                        debug!("type kind {:?}", ty.kind());
                        debug!("unimplemented constant {:?}", literal);
                        result = &ConstantDomain::Unimplemented;
                    }
                };
            }
            _ => {
                debug!("span: {:?}", self.bv.current_span);
                debug!("type kind {:?}", ty.kind());
                debug!("unimplemented constant {:?}", literal);
                result = &ConstantDomain::Unimplemented;
            }
        };
        Rc::new(result.clone().into())
    }

    /// Use for constants that are accessed via references
    #[logfn_inputs(TRACE)]
    fn get_reference_to_constant(
        &mut self,
        val: &rustc_middle::ty::ConstKind<'tcx>,
        ty: Ty<'tcx>,
    ) -> Rc<AbstractValue> {
        match val {
            rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Ptr(p))) => {
                if let Some(rustc_middle::mir::interpret::GlobalAlloc::Static(def_id)) =
                    self.bv.tcx.get_global_alloc(p.alloc_id)
                {
                    return AbstractValue::make_reference(Path::new_static(self.bv.tcx, def_id));
                }
                debug!("span: {:?}", self.bv.current_span);
                debug!("type kind {:?}", ty.kind());
                debug!("ptr {:?}", p);
                assume_unreachable!();
            }
            rustc_middle::ty::ConstKind::Value(ConstValue::Slice { data, start, end }) => {
                self.get_reference_to_slice(ty.kind(), *data, *start, *end)
            }
            _ => {
                debug!("span: {:?}", self.bv.current_span);
                debug!("type kind {:?}", ty.kind());
                debug!("unimplemented constant {:?}", val);
                assume_unreachable!();
            }
        }
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
        if let rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Raw {
            data, ..
        })) = val
        {
            let param_env = self.bv.type_visitor.get_param_env();
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
                                    sign_extend(discr.val, discr_layout.size)
                                } else {
                                    truncate(discr.val, discr_layout.size)
                                }
                            }
                            None => truncate(index.as_u32() as u128, discr_layout.size),
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
                                    sign_extend(*data, tag_layout.size)
                                } else {
                                    *data
                                };
                                discr_bits = truncate(v, discr_layout.size);

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
                                // There exists one single dataful variant (Some(char)).
                                // Other variants are encoded as niches with tag values starting as niche_start.
                                let variants_start = niche_variants.start().as_u32();
                                let variant = if *data >= niche_start {
                                    discr_has_data = false;
                                    let variant_index_relative = (*data - niche_start) as u32;
                                    let variant_index = variants_start + variant_index_relative;
                                    VariantIdx::from_u32(variant_index)
                                } else {
                                    discr_has_data = true;
                                    let fields = &variants[dataful_variant].fields;
                                    checked_assume!(
                                        fields.count() == 1
                                            && fields.offset(0).bytes() == 0
                                            && fields.memory_index(0) == 0,
                                        "the dataful variant should contain a single sub-component"
                                    );
                                    dataful_variant
                                };
                                discr_bits = truncate(variant.as_u32() as u128, discr_layout.size);
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
                        let content_data = self.get_u128_const_val(*data);
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
                    let d = self.get_u128_const_val(*data);
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
        data: u128,
        size: u8,
    ) -> &ConstantDomain {
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
            _ => assume_unreachable!(),
        }
    }

    /// Used only for `&[u8]` and `&str`
    #[logfn_inputs(TRACE)]
    fn get_reference_to_slice(
        &mut self,
        ty: &TyKind<'tcx>,
        data: &'tcx mir::interpret::Allocation,
        start: usize,
        end: usize,
    ) -> Rc<AbstractValue> {
        // The rust compiler should ensure this.
        assume!(end >= start);
        let slice_len = end - start;
        let bytes = data
            .get_bytes(
                &self.bv.tcx,
                // invent a pointer, only the offset is relevant anyway
                mir::interpret::Pointer::new(
                    mir::interpret::AllocId(0),
                    rustc_target::abi::Size::from_bytes(start as u64),
                ),
                rustc_target::abi::Size::from_bytes(slice_len as u64),
            )
            .unwrap();
        let slice = &bytes[start..end];
        match ty {
            TyKind::Ref(_, ty, _) => match ty.kind() {
                TyKind::Array(elem_type, ..) | TyKind::Slice(elem_type) => self
                    .deconstruct_reference_to_constant_array(
                        slice,
                        elem_type.kind().into(),
                        None,
                        ty,
                    ),
                TyKind::Str => {
                    let s = std::str::from_utf8(slice).expect("non utf8 str");
                    let string_const = &mut self.bv.cv.constant_value_cache.get_string_for(s);
                    let string_val: Rc<AbstractValue> = Rc::new(string_const.clone().into());
                    let len_val: Rc<AbstractValue> =
                        Rc::new(ConstantDomain::U128(s.len() as u128).into());

                    let str_path = Path::new_alias(string_val.clone());
                    self.bv
                        .current_environment
                        .update_value_at(str_path.clone(), string_val);

                    let len_path = Path::new_length(str_path.clone());
                    self.bv
                        .current_environment
                        .update_value_at(len_path, len_val);
                    AbstractValue::make_reference(str_path)
                }
                _ => assume_unreachable!(),
            },
            _ => assume_unreachable!(),
        }
    }

    /// Synthesizes a reference to a constant array.
    #[logfn_inputs(TRACE)]
    fn visit_reference_to_array_constant(
        &mut self,
        val: &rustc_middle::ty::ConstKind<'tcx>,
        ty: Ty<'tcx>,
        elem_type: Ty<'tcx>,
        length: &rustc_middle::ty::Const<'tcx>,
    ) -> Rc<AbstractValue> {
        if let rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(
            Scalar::Raw { data, .. },
            ..,
        )) = &length.val
        {
            let len = *data;
            let e_type = ExpressionType::from(elem_type.kind());
            match val {
                rustc_middle::ty::ConstKind::Value(ConstValue::Slice { data, start, end }) => {
                    // The Rust compiler should ensure this.
                    assume!(*end > *start);
                    let slice_len = *end - *start;
                    let bytes = data
                        .get_bytes(
                            &self.bv.tcx,
                            // invent a pointer, only the offset is relevant anyway
                            mir::interpret::Pointer::new(
                                mir::interpret::AllocId(0),
                                rustc_target::abi::Size::from_bytes(*start as u64),
                            ),
                            rustc_target::abi::Size::from_bytes(slice_len as u64),
                        )
                        .unwrap();
                    let slice = &bytes[*start..*end];
                    self.deconstruct_reference_to_constant_array(slice, e_type, Some(len), ty)
                }
                rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(
                    mir::interpret::Scalar::Ptr(ptr),
                )) => {
                    if let Some(rustc_middle::mir::interpret::GlobalAlloc::Static(def_id)) =
                        self.bv.tcx.get_global_alloc(ptr.alloc_id)
                    {
                        return AbstractValue::make_reference(Path::new_static(
                            self.bv.tcx,
                            def_id,
                        ));
                    }
                    let alloc = self.bv.tcx.global_alloc(ptr.alloc_id).unwrap_memory();
                    let alloc_len = alloc.len() as u64;
                    let offset_bytes = ptr.offset.bytes();
                    // The Rust compiler should ensure this.
                    assume!(alloc_len > offset_bytes);
                    let num_bytes = alloc_len - offset_bytes;
                    let bytes = alloc
                        .get_bytes(
                            &self.bv.tcx,
                            *ptr,
                            rustc_target::abi::Size::from_bytes(num_bytes),
                        )
                        .unwrap();
                    self.deconstruct_reference_to_constant_array(&bytes, e_type, Some(len), ty)
                }
                _ => {
                    debug!("unsupported val of type Ref: {:?}", val);
                    unimplemented!();
                }
            }
        } else {
            debug!("unsupported array length: {:?}", length);
            unimplemented!();
        }
    }

    /// Deserializes the given bytes into a constant array of the given element type and then
    /// stores the array elements in the environment with a path for each element, rooted
    /// in a new heap block that represents the array itself and which is returned
    /// as the result of this function. The caller should then copy the path tree to the target
    /// root known to the caller. Since the array is a compile time constant, there is no storage
    /// that needs to get freed or moved.
    ///
    /// The optional length is available as a separate compile time constant in the case of byte string
    /// constants. It is passed in here to check against the length of the bytes array as a safety check.
    #[logfn_inputs(TRACE)]
    fn deconstruct_reference_to_constant_array(
        &mut self,
        bytes: &[u8],
        elem_type: ExpressionType,
        len: Option<u128>,
        array_ty: Ty<'tcx>,
    ) -> Rc<AbstractValue> {
        let byte_len = bytes.len();
        let alignment = self.get_u128_const_val((elem_type.bit_length() / 8) as u128);
        let byte_len_value = self.get_u128_const_val(byte_len as u128);
        let array_value = self
            .bv
            .get_new_heap_block(byte_len_value, alignment, false, array_ty);
        let array_path = Path::get_as_path(array_value);
        let mut last_index: u128 = 0;
        let mut value_map = self.bv.current_environment.value_map.clone();
        for (i, operand) in self
            .get_element_values(bytes, elem_type, len)
            .into_iter()
            .enumerate()
        {
            last_index = i as u128;
            if i < k_limits::MAX_BYTE_ARRAY_LENGTH {
                let index_value = self.get_u128_const_val(last_index);
                let index_path = Path::new_index(array_path.clone(), index_value);
                value_map.insert_mut(index_path, operand);
            }
        }
        let length_path = Path::new_length(array_path.clone());
        let length_value = self.get_u128_const_val(last_index + 1);
        self.bv.current_environment.value_map = value_map.insert(length_path, length_value);
        AbstractValue::make_reference(array_path)
    }

    /// A helper for deconstruct_reference_to_constant_array. See its comments.
    /// This does the deserialization part, whereas deconstruct_constant_array does the environment
    /// updates.
    #[logfn_inputs(TRACE)]
    fn get_element_values(
        &mut self,
        bytes: &[u8],
        elem_type: ExpressionType,
        len: Option<u128>,
    ) -> Vec<Rc<AbstractValue>> {
        let is_signed_type = elem_type.is_signed_integer();
        let bytes_per_elem = (elem_type.bit_length() / 8) as usize;
        if let Some(len) = len {
            checked_assume_eq!(
                len * (bytes_per_elem as u128),
                u128::try_from(bytes.len()).unwrap()
            );
        }
        let chunks = bytes.chunks_exact(bytes_per_elem);
        if is_signed_type {
            fn get_signed_element_value(bytes: &[u8]) -> i128 {
                match bytes.len() {
                    1 => i128::from(bytes[0] as i8),
                    2 => i128::from(i16::from_ne_bytes(bytes.try_into().unwrap())),
                    4 => i128::from(i32::from_ne_bytes(bytes.try_into().unwrap())),
                    8 => i128::from(i64::from_ne_bytes(bytes.try_into().unwrap())),
                    16 => i128::from_ne_bytes(bytes.try_into().unwrap()),
                    _ => assume_unreachable!(),
                }
            }

            let signed_numbers = chunks.map(get_signed_element_value);
            signed_numbers
                .map(|n| Rc::new(ConstantDomain::I128(n).into()))
                .collect()
        } else {
            fn get_unsigned_element_value(bytes: &[u8]) -> u128 {
                match bytes.len() {
                    1 => u128::from(bytes[0]),
                    2 => u128::from(u16::from_ne_bytes(bytes.try_into().unwrap())),
                    4 => u128::from(u32::from_ne_bytes(bytes.try_into().unwrap())),
                    8 => u128::from(u64::from_ne_bytes(bytes.try_into().unwrap())),
                    16 => u128::from_ne_bytes(bytes.try_into().unwrap()),
                    _ => assume_unreachable!(),
                }
            }

            let unsigned_numbers = chunks.map(get_unsigned_element_value);
            unsigned_numbers
                .map(|n| Rc::new(ConstantDomain::U128(n).into()))
                .collect()
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
        generic_args: SubstsRef<'tcx>,
    ) -> &ConstantDomain {
        //todo: is def_id unique enough? Perhaps add ty?
        self.bv.cv.substs_cache.insert(def_id, generic_args);
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
    pub fn visit_place(&mut self, place: &mir::Place<'tcx>) -> Rc<Path> {
        let place_path = self.get_path_for_place(place);
        let mut path = place_path.refine_paths(&self.bv.current_environment, 0);
        match &place_path.value {
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } if **selector == PathSelector::Deref => {
                let refined_qualifier = qualifier.refine_paths(&self.bv.current_environment, 0);
                let qualifier_ty = self
                    .bv
                    .type_visitor
                    .get_path_rustc_type(&refined_qualifier, self.bv.current_span);
                if let TyKind::Ref(_, t, _) = qualifier_ty.kind() {
                    if let TyKind::Array(..) = t.kind() {
                        // The place path dereferences a qualifier that type checks as a pointer.
                        // After refinement we know that the qualifier is a reference to an array.
                        // This means that the current value of path ended up as the refinement of
                        // *&p which reduced to p, which is of type array. The point of all this
                        // aliasing is to get to the first element of the array, so just go there
                        // directly.
                        path = Path::new_index(path, Rc::new(0u128.into()));
                    }
                }
            }
            _ => {}
        }
        let ty = self
            .bv
            .type_visitor
            .get_rustc_place_type(place, self.bv.current_span);

        match &path.value {
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } if **selector == PathSelector::Deref => {
                if let PathEnum::Alias { value } = &qualifier.value {
                    match &value.expression {
                        Expression::Join { left, right, .. } => {
                            let target_type = ExpressionType::from(ty.kind());
                            let distributed_deref = left
                                .dereference(target_type.clone())
                                .join(right.dereference(target_type), &place_path);
                            path = Path::get_as_path(distributed_deref);
                        }
                        Expression::WidenedJoin { operand, .. } => {
                            let target_type = ExpressionType::from(ty.kind());
                            let distributed_deref =
                                operand.dereference(target_type).widen(&place_path);
                            path = Path::get_as_path(distributed_deref);
                        }
                        _ => (),
                    }
                }
            }
            _ => (),
        };
        if !self.bv.type_visitor.path_ty_cache.contains_key(&path) {
            self.bv.type_visitor.path_ty_cache.insert(path.clone(), ty);
        }
        path
    }

    /// Returns a Path instance that is the essentially the same as the Place instance, but which
    /// can be serialized and used as a cache key. Also caches the place type with the path as key.
    /// The path is not normalized so deref selectors are left in place until it is determined if
    /// the fat pointer is being dereferenced to get at its target value, or dereferenced to make
    /// a copy of it.
    #[logfn_inputs(TRACE)]
    pub fn visit_place_defer_refinement(&mut self, place: &mir::Place<'tcx>) -> Rc<Path> {
        self.get_path_for_place(place)
    }

    /// Returns a Path instance that is the essentially the same as the Place instance, but which
    /// can be serialized and used as a cache key.
    #[logfn(TRACE)]
    fn get_path_for_place(&mut self, place: &mir::Place<'tcx>) -> Rc<Path> {
        let base_path: Rc<Path> =
            Path::new_local_parameter_or_result(place.local.as_usize(), self.bv.mir.arg_count);
        if place.projection.is_empty() {
            let ty = self
                .bv
                .type_visitor
                .get_rustc_place_type(place, self.bv.current_span);
            match ty.kind() {
                TyKind::Adt(def, ..) => {
                    let ty_name = self.bv.cv.known_names_cache.get(self.bv.tcx, def.did);
                    if ty_name == KnownNames::StdMarkerPhantomData {
                        return Rc::new(PathEnum::PhantomData.into());
                    }
                }
                TyKind::Array(_, len) => {
                    let len_val = self.visit_constant(None, &len);
                    let len_path = Path::new_length(base_path.clone())
                        .refine_paths(&self.bv.current_environment, 0);
                    self.bv
                        .current_environment
                        .update_value_at(len_path, len_val);
                }
                TyKind::Closure(def_id, generic_args)
                | TyKind::Generator(def_id, generic_args, ..) => {
                    let func_const = self.visit_function_reference(*def_id, ty, generic_args);
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
                        let func_const = self.visit_function_reference(*def_id, ty, generic_args);
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
                        generic_args.as_closure().substs,
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
            let ty = self.bv.type_visitor.get_loc_ty(place.local);
            self.visit_projection(base_path, ty, &place.projection)
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
        let mut result = base_path;
        let mut ty: Ty<'_> = base_ty;
        for elem in projection.iter() {
            let selector = self.visit_projection_elem(ty, elem);
            match elem {
                mir::ProjectionElem::Deref => {
                    if let Some(thin_pointer_path) = Path::get_path_to_thin_pointer_at_offset_0(
                        self.bv.tcx,
                        &self.bv.current_environment,
                        &result,
                        ty,
                    ) {
                        let thin_ptr_type = self
                            .bv
                            .type_visitor
                            .get_path_rustc_type(&thin_pointer_path, self.bv.current_span);
                        ty = type_visitor::get_target_type(thin_ptr_type);
                        let deref_path = Path::new_deref(thin_pointer_path);
                        self.bv
                            .type_visitor
                            .path_ty_cache
                            .insert(deref_path.clone(), ty);
                        result = deref_path;
                        continue;
                    }
                    ty = type_visitor::get_target_type(ty);
                }
                mir::ProjectionElem::Field(_, field_ty) => {
                    ty = self.bv.type_visitor.specialize_generic_argument_type(
                        field_ty,
                        &self.bv.type_visitor.generic_argument_map,
                    )
                }
                mir::ProjectionElem::Index(..) | mir::ProjectionElem::ConstantIndex { .. } => {
                    ty = type_visitor::get_element_type(ty);
                }
                mir::ProjectionElem::Downcast(..) | mir::ProjectionElem::Subslice { .. } => {}
            }
            result = Path::new_qualified(result, Rc::new(selector))
                .refine_paths(&self.bv.current_environment, 0);
            self.bv
                .type_visitor
                .path_ty_cache
                .insert(result.clone(), ty);
        }
        result
    }

    /// Returns a PathSelector instance that is essentially the same as the ProjectionElem instance
    /// but which can be serialized.
    #[logfn_inputs(TRACE)]
    fn visit_projection_elem(
        &mut self,
        base_ty: Ty<'_>,
        projection_elem: &mir::ProjectionElem<mir::Local, &rustc_middle::ty::TyS<'tcx>>,
    ) -> PathSelector {
        match projection_elem {
            mir::ProjectionElem::Deref => PathSelector::Deref,
            mir::ProjectionElem::Field(field, ..) => {
                if let TyKind::Adt(adt_def, _) = base_ty.kind() {
                    if adt_def.is_union() {
                        let variants = &adt_def.variants;
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
                let local_path =
                    Path::new_local_parameter_or_result(local.as_usize(), self.bv.mir.arg_count);
                let index_value = self
                    .bv
                    .lookup_path_and_refine_result(local_path, self.bv.tcx.types.usize);
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
