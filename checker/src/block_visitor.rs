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
use crate::utils;
use crate::{abstract_value, type_visitor};

use log_derive::*;
use mirai_annotations::*;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::ty::adjustment::PointerCast;
use rustc_middle::ty::subst::SubstsRef;
use rustc_middle::ty::{Const, ParamConst, Ty, TyKind, UserTypeAnnotationIndex};
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
        }

        if let Some(mir::Terminator {
            ref source_info,
            ref kind,
        }) = *terminator
        {
            self.visit_terminator(location, *source_info, kind);
        }
    }

    /// Calls a specialized visitor for each kind of statement.
    #[logfn_inputs(TRACE)]
    fn visit_statement(&mut self, location: mir::Location, statement: &mir::Statement<'tcx>) {
        trace!("env {:?}", self.bv.current_environment);
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
            mir::StatementKind::LlvmInlineAsm(inline_asm) => self.visit_inline_asm(inline_asm),
            mir::StatementKind::Retag(retag_kind, place) => self.visit_retag(*retag_kind, place),
            mir::StatementKind::AscribeUserType(..) => assume_unreachable!(),
            mir::StatementKind::Nop => (),
        }
    }

    /// Write the RHS Rvalue to the LHS Place.
    #[logfn_inputs(TRACE)]
    fn visit_assign(&mut self, place: &mir::Place<'tcx>, rvalue: &mir::Rvalue<'tcx>) {
        let path = self.visit_place(place);
        if PathEnum::PhantomData == path.value {
            // No need to track this data
            return;
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
        let target_path = Path::new_discriminant(self.visit_place(place));
        let index_val = self.get_u128_const_val(variant_index.as_usize() as u128);
        self.bv
            .current_environment
            .update_value_at(target_path, index_val);
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
    fn visit_inline_asm(&mut self, inline_asm: &mir::LlvmInlineAsm<'tcx>) {
        let span = self.bv.current_span;
        let err = self.bv.cv.session.struct_span_warn(
            span,
            "Inline assembly code cannot be analyzed by MIRAI. Unsoundly ignoring this.",
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
    #[logfn_inputs(TRACE)]
    fn visit_terminator(
        &mut self,
        location: mir::Location,
        source_info: mir::SourceInfo,
        kind: &mir::TerminatorKind<'tcx>,
    ) {
        trace!("env {:?}", self.bv.current_environment);
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
                location,
                target,
                unwind,
            } => self.visit_drop(location, *target, *unwind),
            mir::TerminatorKind::DropAndReplace { .. } => assume_unreachable!(),
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                cleanup,
                from_hir_call,
            } => self.visit_call(func, args, destination, *cleanup, *from_hir_call),
            mir::TerminatorKind::Assert {
                cond,
                expected,
                msg,
                target,
                cleanup,
            } => self.visit_assert(cond, *expected, msg, *target, *cleanup),
            mir::TerminatorKind::Yield { .. } => assume_unreachable!(),
            mir::TerminatorKind::GeneratorDrop => assume_unreachable!(),
            mir::TerminatorKind::FalseEdges { .. } => assume_unreachable!(),
            mir::TerminatorKind::FalseUnwind { .. } => assume_unreachable!(),
        }
    }

    /// block should have one successor in the graph; we jump there
    #[logfn_inputs(TRACE)]
    fn visit_goto(&mut self, target: mir::BasicBlock) {
        // Propagate the entry condition to the successor block.
        self.bv.current_environment.exit_conditions = self
            .bv
            .current_environment
            .exit_conditions
            .insert(target, self.bv.current_environment.entry_condition.clone());
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
        let discr = discr.as_int_if_known().unwrap_or(discr);
        for i in 0..values.len() {
            let val: Rc<AbstractValue> = Rc::new(ConstantDomain::U128(values[i]).into());
            let cond = discr.equals(val);
            let exit_condition = self
                .bv
                .current_environment
                .entry_condition
                .and(cond.clone());
            let not_cond = cond.logical_not();
            default_exit_condition = default_exit_condition.and(not_cond);
            let target = targets[i];
            self.bv.current_environment.exit_conditions = self
                .bv
                .current_environment
                .exit_conditions
                .insert(target, exit_condition);
        }
        self.bv.current_environment.exit_conditions = self
            .bv
            .current_environment
            .exit_conditions
            .insert(targets[values.len()], default_exit_condition);
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
                if return_guard.is_none() {
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
        location: &mir::Place<'tcx>,
        target: mir::BasicBlock,
        unwind: Option<mir::BasicBlock>,
    ) {
        // Propagate the entry condition to the successor blocks.
        self.bv.current_environment.exit_conditions = self
            .bv
            .current_environment
            .exit_conditions
            .insert(target, self.bv.current_environment.entry_condition.clone());
        if let Some(unwind_target) = unwind {
            self.bv.current_environment.exit_conditions =
                self.bv.current_environment.exit_conditions.insert(
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
    ) {
        // This offset is used to distinguish any local variables that leak out from the called function
        // from local variables of the callee function.
        // This situation arises when a structured value stored in a local variable is assigned to
        // a field reachable from a mutable parameter.
        // We assume that no program that does not make MIRAI run out of memory will have more than
        // a million local variables.
        self.bv.fresh_variable_offset += 1_000_000;

        trace!("source location {:?}", self.bv.current_span);
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
            info!(
                "function {} can't be reliably analyzed because it calls an unknown function.",
                utils::summary_key_str(self.bv.tcx, self.bv.def_id),
            );
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

        let func_const = ConstantDomain::Function(func_ref_to_call.clone());
        let func_const_args = &self.get_function_constant_args(&actual_args);
        let mut call_visitor = CallVisitor::new(
            self,
            callee_def_id,
            Some(callee_generic_arguments),
            callee_generic_argument_map.clone(),
            func_const,
        );
        call_visitor.actual_args = &actual_args;
        call_visitor.actual_argument_types = &actual_argument_types;
        call_visitor.cleanup = cleanup;
        call_visitor.destination = *destination;
        call_visitor.callee_fun_val = func_to_call;
        call_visitor.function_constant_args = func_const_args;
        debug!("calling func {:?}", call_visitor.callee_func_ref);
        if call_visitor.handled_as_special_function_call() {
            return;
        }
        let function_summary = call_visitor
            .get_function_summary()
            .unwrap_or_else(Summary::default);
        if call_visitor.block_visitor.bv.check_for_errors
            && (!function_summary.is_computed || function_summary.is_angelic)
        {
            call_visitor.deal_with_missing_summary();
        }
        debug!(
            "summary {:?} {:?}",
            func_ref_to_call.summary_cache_key, function_summary
        );
        debug!(
            "pre env {:?}",
            call_visitor.block_visitor.bv.current_environment
        );
        debug!("target {:?} arguments {:?}", destination, actual_args);
        call_visitor.check_preconditions_if_necessary(&function_summary);
        call_visitor.transfer_and_refine_normal_return_state(&function_summary);
        call_visitor.transfer_and_refine_cleanup_state(&function_summary);
        debug!(
            "post env {:?}",
            call_visitor.block_visitor.bv.current_environment
        );
        if function_summary.post_condition.is_some() {
            if let Some((_, b)) = &call_visitor.destination {
                debug!(
                    "post exit conditions {:?}",
                    self.bv.current_environment.exit_conditions.get(b)
                );
            }
        }
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
                if self.bv.check_for_errors {
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
                match closure_ty.kind {
                    TyKind::Closure(def_id, substs) => {
                        let specialized_substs = self
                            .bv
                            .type_visitor
                            .specialize_substs(substs, &self.bv.type_visitor.generic_argument_map);
                        return extract_func_ref(self.visit_function_reference(
                            def_id,
                            closure_ty,
                            specialized_substs,
                        ));
                    }
                    TyKind::Ref(_, ty, _) => {
                        if let TyKind::Closure(def_id, substs) = ty.kind {
                            let specialized_substs = self.bv.type_visitor.specialize_substs(
                                substs,
                                &self.bv.type_visitor.generic_argument_map,
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

    pub fn get_i128_const_val(&mut self, val: i128) -> Rc<AbstractValue> {
        self.bv.get_i128_const_val(val)
    }

    pub fn get_u128_const_val(&mut self, val: u128) -> Rc<AbstractValue> {
        self.bv.get_u128_const_val(val)
    }

    /// Emit a diagnostic to the effect that the current call might violate a the given precondition
    /// of the called function. Use the provenance and spans of the precondition to point out related locations.
    #[logfn_inputs(TRACE)]
    pub fn emit_diagnostic_for_precondition(&mut self, precondition: &Precondition, warn: bool) {
        precondition!(self.bv.check_for_errors);
        let mut diagnostic = if warn {
            Rc::new(format!("possible {}", precondition.message))
        } else {
            precondition.message.clone()
        };
        if precondition.spans.is_empty() {
            if let Some(provenance) = &precondition.provenance {
                let mut buffer = diagnostic.to_string();
                buffer.push_str(", defined in ");
                buffer.push_str(provenance.as_str());
                diagnostic = Rc::new(buffer);
            }
        }
        let span = self.bv.current_span;
        let mut err = self
            .bv
            .cv
            .session
            .struct_span_warn(span, diagnostic.as_str());
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
        message: Rc<String>,
        is_post_condition: bool,
    ) -> Option<String> {
        precondition!(self.bv.check_for_errors);
        if cond.is_bottom() {
            return None;
        }
        let (cond_as_bool, entry_cond_as_bool) = self.check_condition_value_and_reachability(cond);

        // If we never get here, rather call unreachable!()
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
                    let message = Rc::new(format!("possible {}", message));
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
            || self.bv.preconditions.len() >= k_limits::MAX_INFERRED_PRECONDITIONS
        {
            // We expect public functions to have programmer supplied preconditions
            // that preclude any assertions from failing. So, at this stage we get to
            // complain a bit.
            let span = self.bv.current_span;
            let warning = self.bv.cv.session.struct_span_warn(span, warning.as_str());
            self.bv.emit_diagnostic(warning);
        }

        Some(warning)
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
                self.bv.current_environment.exit_conditions = self
                    .bv
                    .current_environment
                    .exit_conditions
                    .insert(cleanup_target, panic_exit_condition);
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
            self.bv.current_environment.exit_conditions = self
                .bv
                .current_environment
                .exit_conditions
                .insert(target, normal_exit_condition);

            // Check the condition and issue a warning or infer a precondition.
            if self.bv.check_for_errors {
                if let mir::Operand::Constant(..) = cond {
                    // Do not complain about compile time constants known to the compiler.
                    // Leave that to the compiler.
                } else {
                    let (cond_as_bool_opt, entry_cond_as_bool) =
                        self.check_condition_value_and_reachability(&cond_val);

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
                        let message = Rc::new(String::from(get_assert_msg_description(msg)));
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

    /// Checks the given condition value and also checks if the current entry condition can be true.
    /// If the abstract domains are undecided, resort to using the SMT solver.
    /// Only call this when doing actual error checking, since this is expensive.
    #[logfn_inputs(TRACE)]
    #[logfn(TRACE)]
    pub fn check_condition_value_and_reachability(
        &mut self,
        cond_val: &Rc<AbstractValue>,
    ) -> (Option<bool>, Option<bool>) {
        trace!(
            "entry condition {:?}",
            self.bv.current_environment.entry_condition
        );
        // Check if the condition is always true (or false) if we get here.
        let mut cond_as_bool = cond_val.as_bool_if_known();
        // Check if we can prove that every call to the current function will reach this call site.
        let mut entry_cond_as_bool = self
            .bv
            .current_environment
            .entry_condition
            .as_bool_if_known();
        // Use SMT solver if need be.
        if let Some(entry_cond_as_bool) = entry_cond_as_bool {
            if entry_cond_as_bool && cond_as_bool.is_none() {
                cond_as_bool = self.solve_condition(cond_val);
            }
        } else {
            // Check if path implies condition
            if cond_as_bool.unwrap_or(false)
                || self
                    .bv
                    .current_environment
                    .entry_condition
                    .implies(cond_val)
            {
                return (Some(true), None);
            }
            if !cond_as_bool.unwrap_or(true)
                || self
                    .bv
                    .current_environment
                    .entry_condition
                    .implies_not(cond_val)
            {
                return (Some(false), None);
            }
            // The abstract domains are unable to decide if the entry condition is always true.
            // (If it could decide that the condition is always false, we wouldn't be here.)
            // See if the SMT solver can prove that the entry condition is always true.
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
            if cond_as_bool.is_none() && entry_cond_as_bool.unwrap_or(true) {
                // The abstract domains are unable to decide what the value of cond is.
                cond_as_bool = self.solve_condition(cond_val)
            }
            self.bv.smt_solver.backtrack();
        }
        (cond_as_bool, entry_cond_as_bool)
    }

    #[logfn_inputs(TRACE)]
    fn solve_condition(&mut self, cond_val: &Rc<AbstractValue>) -> Option<bool> {
        let ce = &cond_val.expression;
        let cond_smt_expr = self.bv.smt_solver.get_as_smt_predicate(ce);
        match self.bv.smt_solver.solve_expression(&cond_smt_expr) {
            SmtResult::Unsatisfiable => {
                // If we get here, the solver can prove that cond_val is always false.
                Some(false)
            }
            SmtResult::Satisfiable => {
                // We could get here with cond_val being true. Or perhaps not.
                // So lets see if !cond_val is provably false.
                let not_cond_expr = &cond_val.logical_not().expression;
                let smt_expr = self.bv.smt_solver.get_as_smt_predicate(not_cond_expr);
                if self.bv.smt_solver.solve_expression(&smt_expr) == SmtResult::Unsatisfiable {
                    // The solver can prove that !cond_val is always false.
                    Some(true)
                } else {
                    None
                }
            }
            _ => None,
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
                if self
                    .bv
                    .type_visitor
                    .starts_with_slice_pointer(&rh_type.kind)
                {
                    // todo: visit_constant should probably always return a reference
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
            Path::new_slice(path, length_value).refine_paths(&self.bv.current_environment);
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
        let value_path = self.visit_place(place);
        let value = match &self.visit_place_defer_refinement(place).value {
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } if *selector.as_ref() == PathSelector::Deref => {
                // We are taking a reference to the result of a deref. This is a bit awkward.
                // The deref essentially does a copy of the value denoted by the qualifier.
                // If this value is structured and not heap allocated, the copy must be done
                // with copy_or_move_elements.
                if self
                    .bv
                    .type_visitor
                    .starts_with_slice_pointer(&target_type.kind)
                {
                    // Copying to a fat pointer without a cast, so the source pointer is fat too.
                    // qualifier, however, has been modified into a thin pointer because of the deref.
                    // Undo the damage by stripping off the field 0.
                    if let PathEnum::QualifiedPath {
                        qualifier,
                        selector,
                        ..
                    } = &qualifier.value
                    {
                        if matches!(selector.as_ref(), PathSelector::Field(0)) {
                            self.bv.copy_or_move_elements(
                                path,
                                qualifier.refine_paths(&self.bv.current_environment),
                                target_type,
                                false,
                            );
                            return;
                        }
                    }
                    assume_unreachable!(
                        "apparently assigning a thin pointer to a fat pointer without a cast {:?}",
                        self.bv.current_span
                    );
                } else {
                    self.bv
                        .copy_or_move_elements(path, qualifier.clone(), target_type, false);
                    return;
                }
            }
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                // We are taking a reference to a path that may be rooted in a local that
                // itself contains a reference. We'd like to eliminate that local to keep
                // paths canonical and to avoid leaking locals into summaries.
                let refined_qualifier = qualifier.refine_paths(&self.bv.current_environment);
                if refined_qualifier != *qualifier {
                    let refined_path = Path::new_qualified(refined_qualifier, selector.clone());
                    AbstractValue::make_reference(refined_path)
                } else {
                    AbstractValue::make_reference(value_path)
                }
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
            _ => AbstractValue::make_reference(value_path),
        };
        self.bv.current_environment.update_value_at(path, value);
    }

    /// path = length of a [X] or [X;n] value.
    #[logfn_inputs(TRACE)]
    fn visit_len(&mut self, path: Rc<Path>, place: &mir::Place<'tcx>) {
        let place_ty = self
            .bv
            .type_visitor
            .get_rustc_place_type(place, self.bv.current_span);
        let len_value = if let TyKind::Array(_, len) = &place_ty.kind {
            // We only get here if "-Z mir-opt-level=0" was specified.
            // With more optimization the len instruction becomes a constant.
            self.visit_constant(None, &len)
        } else {
            let mut value_path = self.visit_place(place);
            if let PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } = &value_path.value
            {
                if let PathSelector::Deref = selector.as_ref() {
                    if let PathEnum::QualifiedPath {
                        qualifier,
                        selector,
                        ..
                    } = &qualifier.value
                    {
                        checked_assume!(matches!(selector.as_ref(), PathSelector::Field(0)));
                        value_path = qualifier.clone();
                    } else {
                        value_path = qualifier.clone();
                    }
                } else {
                    assume_unreachable!("{:?}", selector);
                }
            }
            let length_path =
                Path::new_length(value_path).refine_paths(&self.bv.current_environment);
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
                    if self.bv.type_visitor.starts_with_slice_pointer(&ty.kind) {
                        // Note that the source could be a thin or fat pointer.
                        if !self
                            .bv
                            .type_visitor
                            .starts_with_slice_pointer(&source_type.kind)
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
                            let len_value = if let TyKind::Array(_, len) = &target_type.kind {
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
                    .cast(ExpressionType::from(&ty.kind));
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
        let path0 = Path::new_field(path.clone(), 0).refine_paths(&self.bv.current_environment);
        self.bv.current_environment.update_value_at(path0, result);
        let path1 = Path::new_field(path, 1).refine_paths(&self.bv.current_environment);
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
                .refine_paths(&self.bv.current_environment);
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
    fn visit_constant(
        &mut self,
        user_ty: Option<UserTypeAnnotationIndex>,
        literal: &Const<'tcx>,
    ) -> Rc<AbstractValue> {
        let ty = literal.ty;

        match &literal.val {
            rustc_middle::ty::ConstKind::Unevaluated(def_id, substs, promoted) => {
                let substs = self
                    .bv
                    .type_visitor
                    .specialize_substs(substs, &self.bv.type_visitor.generic_argument_map);
                self.bv.cv.substs_cache.insert(*def_id, substs);
                let name = utils::summary_key_str(self.bv.tcx, *def_id);
                let expression_type: ExpressionType = ExpressionType::from(&ty.kind);
                let path = match promoted {
                    Some(promoted) => {
                        let index = promoted.index();
                        Rc::new(PathEnum::PromotedConstant { ordinal: index }.into())
                    }
                    None => Rc::new(
                        PathEnum::StaticVariable {
                            def_id: Some(*def_id),
                            summary_cache_key: name,
                            expression_type,
                        }
                        .into(),
                    ),
                };
                self.bv.lookup_path_and_refine_result(path, ty)
            }

            _ => {
                let result;
                match ty.kind {
                    TyKind::Bool
                    | TyKind::Char
                    | TyKind::Float(..)
                    | TyKind::Int(..)
                    | TyKind::Uint(..) => match &literal.val {
                        rustc_middle::ty::ConstKind::Param(ParamConst { index, .. }) => {
                            if let Some(gen_args) = self.bv.type_visitor.generic_arguments {
                                if let Some(arg_val) = gen_args.as_ref().get(*index as usize) {
                                    return self.visit_constant(None, arg_val.expect_const());
                                }
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
                            result = self.get_constant_from_scalar(&ty.kind, *data, *size);
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
                        let substs = self
                            .bv
                            .type_visitor
                            .specialize_substs(substs, &self.bv.type_visitor.generic_argument_map);
                        result = self.visit_function_reference(def_id, ty, substs);
                    }
                    TyKind::Ref(
                        _,
                        &rustc_middle::ty::TyS {
                            kind: TyKind::Str, ..
                        },
                        _,
                    ) => {
                        if let rustc_middle::ty::ConstKind::Value(ConstValue::Slice {
                            data,
                            start,
                            end,
                        }) = &literal.val
                        {
                            return self.get_value_from_slice(&ty.kind, data, *start, *end);
                        } else {
                            debug!("unsupported val of type Ref: {:?}", literal);
                            unimplemented!();
                        };
                    }
                    TyKind::Ref(
                        _,
                        &rustc_middle::ty::TyS {
                            kind: TyKind::Array(elem_type, length),
                            ..
                        },
                        _,
                    ) => {
                        return self.visit_reference_to_array_constant(literal, elem_type, length);
                    }
                    TyKind::Ref(
                        _,
                        &rustc_middle::ty::TyS {
                            kind: TyKind::Slice(elem_type),
                            ..
                        },
                        _,
                    ) => match &literal.val {
                        rustc_middle::ty::ConstKind::Value(ConstValue::Slice {
                            data,
                            start,
                            end,
                        }) => {
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
                            let e_type = ExpressionType::from(&elem_type.kind);
                            return self.deconstruct_reference_to_constant_array(
                                slice,
                                e_type,
                                None,
                                type_visitor::get_target_type(ty),
                            );
                        }
                        rustc_middle::ty::ConstKind::Value(ConstValue::ByRef { alloc, offset }) => {
                            let e_type = ExpressionType::from(&elem_type.kind);
                            let id = self.bv.tcx.alloc_map.lock().create_memory_alloc(alloc);
                            let len = alloc.len() as u64;
                            let offset_in_bytes: u64 = offset.bytes();
                            // The rust compiler should ensure this.
                            assume!(len > offset_in_bytes);
                            let num_bytes = len - offset_in_bytes;
                            let ptr = mir::interpret::Pointer::new(id, *offset);
                            //todo: this is all wrong. It gets the bytes that contains the reference,
                            // not the bytes that the reference points to.
                            // Right now it is not clear how to implement this.
                            // Keeping this wrong behavior maintains the currently incorrect status quo.
                            let bytes = alloc
                                .get_bytes_with_undef_and_ptr(
                                    &self.bv.tcx,
                                    ptr,
                                    rustc_target::abi::Size::from_bytes(num_bytes),
                                )
                                .unwrap();
                            return self.deconstruct_reference_to_constant_array(
                                &bytes,
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
                    | TyKind::Ref(_, ty, rustc_hir::Mutability::Mut) => match &literal.val {
                        rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Ptr(p))) => {
                            let summary_cache_key = format!("{:?}", p).into();
                            let expression_type: ExpressionType = ExpressionType::from(&ty.kind);
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
                        return self.get_reference_to_constant(literal, ty);
                    }
                    TyKind::Adt(adt_def, _) if adt_def.is_enum() => {
                        return self.get_enum_variant_as_constant(literal, ty);
                    }
                    TyKind::Tuple(..) | TyKind::Adt(..) => {
                        match &literal.val {
                            rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(
                                Scalar::Raw { size: 0, .. },
                            )) => {
                                return self.bv.get_new_heap_block(
                                    Rc::new(0u128.into()),
                                    Rc::new(1u128.into()),
                                    false,
                                    ty,
                                );
                            }
                            _ => {
                                debug!("span: {:?}", self.bv.current_span);
                                debug!("type kind {:?}", ty.kind);
                                debug!("unimplemented constant {:?}", literal);
                                result = &ConstantDomain::Unimplemented;
                            }
                        };
                    }
                    _ => {
                        debug!("span: {:?}", self.bv.current_span);
                        debug!("type kind {:?}", ty.kind);
                        debug!("unimplemented constant {:?}", literal);
                        result = &ConstantDomain::Unimplemented;
                    }
                };
                Rc::new(result.clone().into())
            }
        }
    }

    /// Use for constants that are accessed via references
    #[logfn_inputs(TRACE)]
    fn get_reference_to_constant(
        &mut self,
        literal: &rustc_middle::ty::Const<'tcx>,
        ty: Ty<'tcx>,
    ) -> Rc<AbstractValue> {
        match &literal.val {
            rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Ptr(p))) => {
                if let Some(rustc_middle::mir::interpret::GlobalAlloc::Static(def_id)) =
                    self.bv.tcx.alloc_map.lock().get(p.alloc_id)
                {
                    let name = utils::summary_key_str(self.bv.tcx, def_id);
                    let expression_type: ExpressionType = ExpressionType::from(&ty.kind);
                    let path = Rc::new(
                        PathEnum::StaticVariable {
                            def_id: Some(def_id),
                            summary_cache_key: name,
                            expression_type,
                        }
                        .into(),
                    );
                    return AbstractValue::make_reference(path);
                }
                debug!("span: {:?}", self.bv.current_span);
                debug!("type kind {:?}", ty.kind);
                debug!("ptr {:?}", p);
                assume_unreachable!();
            }
            rustc_middle::ty::ConstKind::Value(ConstValue::Slice { data, start, end }) => {
                self.get_value_from_slice(&ty.kind, *data, *start, *end)
            }
            _ => {
                debug!("span: {:?}", self.bv.current_span);
                debug!("type kind {:?}", ty.kind);
                debug!("unimplemented constant {:?}", literal);
                assume_unreachable!();
            }
        }
    }
    /// Used for enum typed constants. Currently only simple variants are understood.
    #[logfn_inputs(TRACE)]
    fn get_enum_variant_as_constant(
        &mut self,
        literal: &rustc_middle::ty::Const<'tcx>,
        ty: Ty<'tcx>,
    ) -> Rc<AbstractValue> {
        let result;
        match &literal.val {
            rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Raw { data, size }))
                if *size == 1 =>
            {
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
                verify_unreachable!();
            }
            _ => {
                debug!("span: {:?}", self.bv.current_span);
                debug!("type kind {:?}", ty.kind);
                debug!("unimplemented constant {:?}", literal);
                result = &ConstantDomain::Unimplemented;
            }
        };
        Rc::new(result.clone().into())
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
    fn get_value_from_slice(
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
            TyKind::Ref(_, ty, _) => match ty.kind {
                TyKind::Array(elem_type, ..) | TyKind::Slice(elem_type) => self
                    .deconstruct_reference_to_constant_array(
                        slice,
                        (&elem_type.kind).into(),
                        None,
                        ty,
                    ),
                TyKind::Str => {
                    let s = std::str::from_utf8(slice).expect("non utf8 str");
                    let string_const = &mut self.bv.cv.constant_value_cache.get_string_for(s);
                    let string_val: Rc<AbstractValue> = Rc::new(string_const.clone().into());
                    let len_val: Rc<AbstractValue> =
                        Rc::new(ConstantDomain::U128(s.len() as u128).into());

                    let fat_pointer_path = Path::new_alias(string_val.clone());
                    let pointer_path = Path::new_field(fat_pointer_path.clone(), 0);
                    self.bv
                        .current_environment
                        .update_value_at(pointer_path, string_val.clone());
                    let len_path = Path::new_length(fat_pointer_path);
                    self.bv
                        .current_environment
                        .update_value_at(len_path, len_val);
                    string_val
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
        literal: &rustc_middle::ty::Const<'tcx>,
        elem_type: &rustc_middle::ty::TyS<'tcx>,
        length: &rustc_middle::ty::Const<'tcx>,
    ) -> Rc<AbstractValue> {
        use rustc_middle::mir::interpret::{ConstValue, Scalar};

        if let rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(
            Scalar::Raw { data, .. },
            ..,
        )) = &length.val
        {
            let len = *data;
            let e_type = ExpressionType::from(&elem_type.kind);
            match &literal.val {
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
                    self.deconstruct_reference_to_constant_array(
                        slice,
                        e_type,
                        Some(len),
                        literal.ty,
                    )
                }
                rustc_middle::ty::ConstKind::Value(ConstValue::ByRef { alloc, offset }) => {
                    //todo: there is no test coverage for this case
                    let id = self.bv.tcx.alloc_map.lock().create_memory_alloc(alloc);
                    let alloc_len = alloc.len() as u64;
                    let offset_bytes = offset.bytes();
                    // The Rust compiler should ensure this.
                    assume!(alloc_len > offset_bytes);
                    let num_bytes = alloc_len - offset_bytes;
                    let ptr = mir::interpret::Pointer::new(
                        id,
                        rustc_target::abi::Size::from_bytes(offset.bytes()),
                    );
                    //todo: this is all wrong. It gets the bytes that contains the reference,
                    // not the bytes that the reference points to.
                    // Right now it is not clear how to implement this.
                    // Keeping this wrong behavior maintains the currently incorrect status quo.
                    let bytes = alloc
                        .get_bytes_with_undef_and_ptr(
                            &self.bv.tcx,
                            ptr,
                            rustc_target::abi::Size::from_bytes(num_bytes),
                        )
                        .unwrap();
                    self.deconstruct_reference_to_constant_array(
                        &bytes,
                        e_type,
                        Some(len),
                        literal.ty,
                    )
                }
                rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(
                    mir::interpret::Scalar::Ptr(ptr),
                )) => {
                    if let Some(rustc_middle::mir::interpret::GlobalAlloc::Static(def_id)) =
                        self.bv.tcx.alloc_map.lock().get(ptr.alloc_id)
                    {
                        let name = utils::summary_key_str(self.bv.tcx, def_id);
                        let path = Rc::new(
                            PathEnum::StaticVariable {
                                def_id: Some(def_id),
                                summary_cache_key: name,
                                expression_type: ExpressionType::NonPrimitive,
                            }
                            .into(),
                        );
                        let rustc_ty = self.bv.tcx.type_of(def_id);
                        return self.bv.lookup_path_and_refine_result(path, rustc_ty);
                    }
                    let alloc = self.bv.tcx.alloc_map.lock().unwrap_memory(ptr.alloc_id);
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
                    self.deconstruct_reference_to_constant_array(
                        &bytes,
                        e_type,
                        Some(len),
                        literal.ty,
                    )
                }
                _ => {
                    debug!("unsupported val of type Ref: {:?}", literal);
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
        let array_path = Path::get_as_path(array_value.clone());
        let thin_pointer_path = Path::new_field(array_path.clone(), 0);
        self.bv
            .current_environment
            .update_value_at(thin_pointer_path, array_value);
        let mut last_index: u128 = 0;
        for (i, operand) in self
            .get_element_values(bytes, elem_type, len)
            .into_iter()
            .enumerate()
        {
            last_index = i as u128;
            if i < k_limits::MAX_BYTE_ARRAY_LENGTH {
                let index_value = self.get_u128_const_val(last_index);
                let index_path = Path::new_index(array_path.clone(), index_value);
                self.bv
                    .current_environment
                    .update_value_at(index_path, operand);
            }
        }
        let length_path = Path::new_length(array_path.clone());
        let length_value = self.get_u128_const_val(last_index + 1);
        self.bv
            .current_environment
            .update_value_at(length_path, length_value);
        AbstractValue::make_reference(array_path)
    }

    /// A helper for deconstruct_constant_array. See its comments.
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
    fn visit_function_reference(
        &mut self,
        def_id: DefId,
        ty: Ty<'tcx>,
        generic_args: SubstsRef<'tcx>,
    ) -> &ConstantDomain {
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
        let path = self
            .get_path_for_place(place)
            .refine_paths(&self.bv.current_environment);
        let ty = self
            .bv
            .type_visitor
            .get_rustc_place_type(place, self.bv.current_span);
        self.bv.type_visitor.path_ty_cache.insert(path.clone(), ty);
        path
    }

    /// Returns a Path instance that is the essentially the same as the Place instance, but which
    /// can be serialized and used as a cache key. Also caches the place type with the path as key.
    /// The path is not normalized so deref selectors are left in place until it is determined if
    /// the fat pointer is being dereferenced to get at its target value, or dereferenced to make
    /// a copy of it.
    #[logfn_inputs(TRACE)]
    pub fn visit_place_defer_refinement(&mut self, place: &mir::Place<'tcx>) -> Rc<Path> {
        let path = self.get_path_for_place(place);
        let ty = self
            .bv
            .type_visitor
            .get_rustc_place_type(place, self.bv.current_span);
        self.bv.type_visitor.path_ty_cache.insert(path.clone(), ty);
        path
    }

    /// Returns a Path instance that is the essentially the same as the Place instance, but which
    /// can be serialized and used as a cache key.
    #[logfn(TRACE)]
    fn get_path_for_place(&mut self, place: &mir::Place<'tcx>) -> Rc<Path> {
        let base_path: Rc<Path> =
            Path::new_local_parameter_or_result(place.local.as_usize(), self.bv.mir.arg_count)
                .refine_paths(&self.bv.current_environment);
        if place.projection.is_empty() {
            let ty = self
                .bv
                .type_visitor
                .get_rustc_place_type(place, self.bv.current_span);
            match &ty.kind {
                TyKind::Adt(def, ..) => {
                    let ty_name = self.bv.cv.known_names_cache.get(self.bv.tcx, def.did);
                    if ty_name == KnownNames::StdMarkerPhantomData {
                        return Rc::new(PathEnum::PhantomData.into());
                    }
                }
                TyKind::Array(_, len) => {
                    let len_val = self.visit_constant(None, &len);
                    let len_path = Path::new_length(base_path.clone())
                        .refine_paths(&self.bv.current_environment);
                    self.bv
                        .current_environment
                        .update_value_at(len_path, len_val);
                }
                TyKind::Closure(def_id, generic_args, ..) => {
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
                TyKind::Generator(def_id, generic_args, ..) => {
                    let func_const = self.visit_function_reference(
                        *def_id,
                        ty,
                        generic_args.as_generator().substs,
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
            let ty = self.bv.type_visitor.specialize_generic_argument_type(
                self.bv.mir.local_decls[place.local].ty,
                &self.bv.type_visitor.generic_argument_map,
            );
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
                        // defer refinement of thin_pointer_path until it is clear that it does not
                        // become the operand location for an address_of operation.
                        let deref_path = Path::new_qualified(thin_pointer_path, Rc::new(selector));
                        self.bv
                            .type_visitor
                            .path_ty_cache
                            .insert(deref_path.clone(), ty);
                        result = deref_path;
                        continue;
                    }
                    ty = type_visitor::get_target_type(ty);
                }
                mir::ProjectionElem::Field(_, field_ty) => ty = field_ty,
                mir::ProjectionElem::Index(..) | mir::ProjectionElem::ConstantIndex { .. } => {
                    ty = type_visitor::get_element_type(ty);
                }
                mir::ProjectionElem::Downcast(..) | mir::ProjectionElem::Subslice { .. } => {}
            }
            result = Path::new_qualified(result, Rc::new(selector))
                .refine_paths(&self.bv.current_environment);
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
                PathSelector::Field(if type_visitor::is_union(base_ty) {
                    0
                } else {
                    field.index()
                })
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
                    None => format!("variant#{}", index.as_usize()),
                    Some(name) => String::from(name.as_str().deref()),
                };
                PathSelector::Downcast(Rc::new(name_str), index.as_usize())
            }
        }
    }
}
