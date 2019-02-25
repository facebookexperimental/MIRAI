// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use abstract_domains::AbstractDomain;
use abstract_value::{self, AbstractValue, Path, PathSelector};
use constant_domain::{ConstantDomain, ConstantValueCache};
use environment::Environment;
use expression::{Expression, ExpressionType};
use k_limits;
use rustc::session::Session;
use rustc::ty::{Const, LazyConst, Ty, TyCtxt, TyKind, UserTypeAnnotationIndex};
use rustc::{hir, mir};
use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;
use std::iter::FromIterator;
use summaries;
use summaries::{PersistentSummaryCache, Summary};
use syntax::errors::{Diagnostic, DiagnosticBuilder};
use syntax_pos;
use utils::is_public;

pub struct MirVisitorCrateContext<'a, 'b: 'a, 'tcx: 'b> {
    /// A place where diagnostic messages can be buffered by the test harness.
    pub buffered_diagnostics: &'a mut Vec<Diagnostic>,
    /// A call back that the test harness can use to buffer the diagnostic message.
    /// By default this just calls emit on the diagnostic.
    pub emit_diagnostic: fn(&mut DiagnosticBuilder, buf: &mut Vec<Diagnostic>) -> (),
    pub session: &'tcx Session,
    pub tcx: TyCtxt<'b, 'tcx, 'tcx>,
    pub def_id: hir::def_id::DefId,
    pub mir: &'a mir::Mir<'tcx>,
    pub constant_value_cache: &'a mut ConstantValueCache,
    pub summary_cache: &'a mut PersistentSummaryCache<'b, 'tcx>,
}

/// Holds the state for the MIR test visitor.
pub struct MirVisitor<'a, 'b: 'a, 'tcx: 'b> {
    buffered_diagnostics: &'a mut Vec<Diagnostic>,
    emit_diagnostic: fn(&mut DiagnosticBuilder, buf: &mut Vec<Diagnostic>) -> (),
    session: &'tcx Session,
    tcx: TyCtxt<'b, 'tcx, 'tcx>,
    def_id: hir::def_id::DefId,
    mir: &'a mir::Mir<'tcx>,
    constant_value_cache: &'a mut ConstantValueCache,
    summary_cache: &'a mut PersistentSummaryCache<'b, 'tcx>,

    check_for_errors: bool,
    current_environment: Environment,
    current_location: mir::Location,
    current_span: syntax_pos::Span,
    exit_environment: Environment,
    heap_addresses: HashMap<mir::Location, AbstractValue>,
    post_conditions: Vec<AbstractValue>,
    preconditions: Vec<(AbstractValue, String)>,
    unwind_condition: Option<AbstractValue>,
    unwind_environment: Environment,
}

/// A visitor that simply traverses enough of the MIR associated with a particular code body
/// so that we can test a call to every default implementation of the MirVisitor trait.
impl<'a, 'b: 'a, 'tcx: 'b> MirVisitor<'a, 'b, 'tcx> {
    pub fn new(crate_context: MirVisitorCrateContext<'a, 'b, 'tcx>) -> MirVisitor<'a, 'b, 'tcx> {
        MirVisitor {
            buffered_diagnostics: crate_context.buffered_diagnostics,
            emit_diagnostic: crate_context.emit_diagnostic,
            session: crate_context.session,
            tcx: crate_context.tcx,
            def_id: crate_context.def_id,
            mir: crate_context.mir,
            constant_value_cache: crate_context.constant_value_cache,
            summary_cache: crate_context.summary_cache,

            check_for_errors: false,
            current_environment: Environment::default(),
            current_location: mir::Location::START,
            current_span: syntax_pos::DUMMY_SP,
            exit_environment: Environment::default(),
            heap_addresses: HashMap::default(),
            post_conditions: Vec::new(),
            preconditions: Vec::new(),
            unwind_condition: None,
            unwind_environment: Environment::default(),
        }
    }

    /// Restores the method only state to its initial state.
    fn reset_visitor_state(&mut self) {
        self.check_for_errors = false;
        self.current_environment = Environment::default();
        self.current_location = mir::Location::START;
        self.current_span = syntax_pos::DUMMY_SP;
        self.exit_environment = Environment::default();
        self.heap_addresses = HashMap::default();
        self.post_conditions = Vec::new();
        self.preconditions = Vec::new();
        self.unwind_condition = None;
        self.unwind_environment = Environment::default();
    }

    /// Use the local and global environments to resolve Path to an abstract value.
    /// For now, promoted constants just return Top.
    fn lookup_path_and_refine_result(
        &mut self,
        path: Path,
        result_type: ExpressionType,
    ) -> AbstractValue {
        let refined_val = {
            let bottom = abstract_value::BOTTOM;
            let local_val = self.current_environment.value_at(&path).unwrap_or(&bottom);
            local_val.refine_with(&self.current_environment.entry_condition, self.current_span)
        };
        if refined_val.is_bottom() {
            // Not found locally, so try statics.
            if let Path::StaticVariable {
                def_id,
                ref summary_cache_key,
            } = path
            {
                let mut summary;
                let summary = if let Some(def_id) = def_id {
                    self.summary_cache
                        .get_summary_for(def_id, Some(self.def_id))
                } else {
                    summary = self
                        .summary_cache
                        .get_persistent_summary_for(summary_cache_key);
                    &summary
                };
                summary.result.clone().unwrap_or(abstract_value::TOP)
            } else if path.path_length() < k_limits::MAX_PATH_LENGTH {
                Expression::Variable {
                    path: box path.clone(),
                    var_type: result_type,
                }
                .into()
            } else {
                abstract_value::TOP
            }
        } else {
            refined_val
        }
    }

    /// Lookups up the local definition for this ordinal and maps the type information
    /// onto ExpressionType.
    fn get_type_for_local(&self, ordinal: usize) -> ExpressionType {
        let loc = &self.mir.local_decls[mir::Local::from(ordinal)];
        (&loc.ty.sty).into()
    }

    /// Analyze the body and store a summary of its behavior in self.summary_cache.
    pub fn visit_body(&mut self) {
        debug!("visit_body({:?})", self.def_id);
        // in_state[bb] is the join (or widening) of the out_state values of each predecessor of bb
        let mut in_state: HashMap<mir::BasicBlock, Environment> = HashMap::new();
        // out_state[bb] is the environment that results from analyzing block bb, given in_state[bb]
        let mut out_state: HashMap<mir::BasicBlock, Environment> = HashMap::new();
        for bb in self.mir.basic_blocks().indices() {
            in_state.insert(bb, Environment::default());
            out_state.insert(bb, Environment::default());
        }
        // The entry block has no predecessors and its initial state is the function parameters
        // as well any promoted constants.
        let first_state = self.promote_constants();

        // Compute a fixed point, which is a value of out_state that will not grow with more iterations.
        let mut changed = true;
        let mut iteration_count = 0;
        while changed {
            changed = false;
            for bb in self.mir.basic_blocks().indices() {
                // Merge output states of predecessors of bb
                let i_state = if bb.index() == 0 {
                    first_state.clone()
                } else {
                    let mut predecessor_states_and_conditions: Vec<(
                        &Environment,
                        Option<&AbstractValue>,
                    )> = self
                        .mir
                        .predecessors_for(bb)
                        .iter()
                        .map(|pred_bb| {
                            let pred_state = &out_state[pred_bb];
                            let pred_exit_condition = pred_state.exit_conditions.get(&bb);
                            (pred_state, pred_exit_condition)
                        })
                        .filter(|(_, pred_exit_condition)| pred_exit_condition.is_some())
                        .collect();
                    if predecessor_states_and_conditions.is_empty() {
                        // unreachable block
                        let mut i_state = in_state[&bb].clone();
                        i_state.entry_condition = abstract_value::FALSE;
                        i_state
                    } else {
                        // We want to do right associative operations and that is easier if we reverse.
                        predecessor_states_and_conditions.reverse();
                        let (p_state, pred_exit_condition) = predecessor_states_and_conditions[0];
                        let mut i_state = p_state.clone();
                        i_state.entry_condition = pred_exit_condition
                            .unwrap()
                            .with_provenance(self.current_span);
                        for (p_state, pred_exit_condition) in
                            predecessor_states_and_conditions.iter().skip(1)
                        {
                            let join_condition = pred_exit_condition.unwrap();
                            // Once all paths have already been analyzed for a second time (iteration_count >= 3)
                            // we to abstract more aggressively in order to ensure reaching a fixed point.
                            let mut j_state = if iteration_count < 3 {
                                p_state.join(&i_state, join_condition)
                            } else {
                                p_state.widen(&i_state, join_condition)
                            };
                            j_state.entry_condition = join_condition
                                .or(&i_state.entry_condition, Some(self.current_span));
                            i_state = j_state;
                        }
                        i_state
                    }
                };
                // Analyze the basic block.
                in_state.insert(bb, i_state.clone());
                self.current_environment = i_state;
                self.visit_basic_block(bb);

                // Check for a fixed point.
                if !self.current_environment.subset(&out_state[&bb]) {
                    // There is some path for which self.current_environment.value_at(path) includes
                    // a value this is not present in out_state[bb].value_at(path), so any block
                    // that used out_state[bb] as part of its input state now needs to get reanalyzed.
                    out_state.insert(bb, self.current_environment.clone());
                    changed = true;
                } else {
                    // If the environment at the end of this block does not have any new values,
                    // we have reached a fixed point for this block.
                }
            }
            iteration_count += 1;
        }

        // Now traverse the blocks again, doing checks and emitting diagnostics.
        // in_state[bb] is now complete for every basic block bb in the body.
        debug!(
            "Fixed point loop took {} iterations, now checking for errors.",
            iteration_count
        );
        self.check_for_errors = true;
        for bb in self.mir.basic_blocks().indices() {
            let i_state = (&in_state[&bb]).clone();
            if i_state.entry_condition.as_bool_if_known().unwrap_or(true) {
                self.current_environment = i_state;
                self.visit_basic_block(bb);
            }
        }

        // Now create a summary of the body that can be in-lined into call sites.
        let summary = summaries::summarize(
            self.mir.arg_count,
            &self.exit_environment,
            &self.preconditions,
            &self.post_conditions,
            self.unwind_condition.clone(),
            &self.unwind_environment,
        );
        self.summary_cache.set_summary_for(self.def_id, summary);
    }

    /// Use the visitor to compute the state corresponding to promoted constants.
    fn promote_constants(&mut self) -> Environment {
        let mut state_with_parameters = Environment::default();
        let saved_mir = self.mir;
        let result_root = Path::LocalVariable { ordinal: 0 };
        for (ordinal, constant_mir) in self.mir.promoted.iter().enumerate() {
            self.mir = constant_mir;
            let result_type = self.get_type_for_local(0);
            self.visit_body();

            let promoted_root = Path::PromotedConstant { ordinal };
            let value = self.lookup_path_and_refine_result(result_root.clone(), result_type);
            state_with_parameters.update_value_at(promoted_root.clone(), value);
            for (path, value) in self
                .exit_environment
                .value_map
                .iter()
                .filter(|(p, _)| p.is_rooted_by(&result_root))
            {
                let promoted_path = path.replace_root(&result_root, promoted_root.clone());
                state_with_parameters.update_value_at(promoted_path, value.clone());
            }

            self.reset_visitor_state();
        }
        self.mir = saved_mir;
        state_with_parameters
    }

    /// Visits each statement in order and then visits the terminator.
    fn visit_basic_block(&mut self, bb: mir::BasicBlock) {
        debug!("visit_basic_block({:?})", bb);

        let mir::BasicBlockData {
            ref statements,
            ref terminator,
            ..
        } = &self.mir[bb];
        let mut location = bb.start_location();
        let terminator_index = statements.len();

        while location.statement_index < terminator_index {
            self.visit_statement(location, &statements[location.statement_index]);
            location.statement_index += 1;
        }

        if let Some(mir::Terminator {
            ref source_info,
            ref kind,
        }) = *terminator
        {
            self.visit_terminator(*source_info, kind);
        }
    }

    /// Calls a specialized visitor for each kind of statement.
    fn visit_statement(&mut self, location: mir::Location, statement: &mir::Statement<'tcx>) {
        self.current_location = location;
        let mir::Statement { kind, source_info } = statement;
        debug!("{:?}", source_info);
        self.current_span = source_info.span;
        match kind {
            mir::StatementKind::Assign(place, rvalue) => self.visit_assign(place, rvalue.borrow()),
            mir::StatementKind::FakeRead(..) => unreachable!(),
            mir::StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => self.visit_set_discriminant(place, *variant_index),
            mir::StatementKind::StorageLive(local) => self.visit_storage_live(*local),
            mir::StatementKind::StorageDead(local) => self.visit_storage_dead(*local),
            mir::StatementKind::InlineAsm {
                asm,
                outputs,
                inputs,
            } => self.visit_inline_asm(asm, outputs, inputs),
            mir::StatementKind::Retag(retag_kind, place) => self.visit_retag(*retag_kind, place),
            mir::StatementKind::AscribeUserType(..) => unreachable!(),
            mir::StatementKind::Nop => return,
        }
    }

    /// Write the RHS Rvalue to the LHS Place.
    fn visit_assign(&mut self, place: &mir::Place, rvalue: &mir::Rvalue<'tcx>) {
        debug!(
            "default visit_assign(place: {:?}, rvalue: {:?})",
            place, rvalue
        );
        let path = self.visit_place(place);
        self.visit_rvalue(path, rvalue);
    }

    /// Write the discriminant for a variant to the enum Place.
    fn visit_set_discriminant(
        &mut self,
        place: &mir::Place,
        variant_index: rustc::ty::layout::VariantIdx,
    ) {
        debug!(
            "default visit_set_discriminant(place: {:?}, variant_index: {:?})",
            place, variant_index
        );
        let target_path = self.visit_place(place);
        let index_val = self
            .constant_value_cache
            .get_u128_for(variant_index.as_usize() as u128)
            .clone()
            .into();
        self.current_environment
            .update_value_at(target_path, index_val);
    }

    /// Start a live range for the storage of the local.
    fn visit_storage_live(&mut self, local: mir::Local) {
        debug!("default visit_storage_live(local: {:?})", local);
        let path = Path::LocalVariable {
            ordinal: local.as_usize(),
        };
        self.current_environment
            .update_value_at(path, abstract_value::TOP.clone());
    }

    /// End the current live range for the storage of the local.
    fn visit_storage_dead(&mut self, local: mir::Local) {
        debug!("default visit_storage_dead(local: {:?})", local);
        let path = Path::LocalVariable {
            ordinal: local.as_usize(),
        };
        self.current_environment
            .update_value_at(path, abstract_value::BOTTOM.clone());
    }

    /// Execute a piece of inline Assembly.
    fn visit_inline_asm(
        &mut self,
        asm: &hir::InlineAsm,
        outputs: &[mir::Place],
        inputs: &[(syntax_pos::Span, mir::Operand)],
    ) {
        debug!(
            "default visit_inline_asm(asm: {:?}, outputs: {:?}, inputs: {:?})",
            asm, outputs, inputs
        );
        if self.check_for_errors {
            let span = self.current_span;
            let mut err = self.session.struct_span_warn(
                span,
                "Inline assembly code cannot be analyzed by MIRAI. Unsoundly ignoring this.",
            );
            (self.emit_diagnostic)(&mut err, &mut self.buffered_diagnostics);
        }
    }

    /// Retag references in the given place, ensuring they got fresh tags.  This is
    /// part of the Stacked Borrows model. These statements are currently only interpreted
    /// by miri and only generated when "-Z mir-emit-retag" is passed.
    /// See <https://internals.rust-lang.org/t/stacked-borrows-an-aliasing-model-for-rust/8153/>
    /// for more details.
    fn visit_retag(&self, retag_kind: mir::RetagKind, place: &mir::Place) {
        debug!(
            "default visit_retag(retag_kind: {:?}, place: {:?})",
            retag_kind, place
        );
        // This seems to be an intermediate artifact of MIR generation and is related to aliasing.
        // We assume (and will attempt to enforce) that no aliasing of mutable pointers are present
        // in the programs we check.
        //
        // Therefore we simply ignore this.
    }

    /// Calls a specialized visitor for each kind of terminator.
    fn visit_terminator(&mut self, source_info: mir::SourceInfo, kind: &mir::TerminatorKind) {
        debug!("{:?}", source_info);
        self.current_span = source_info.span;
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
            mir::TerminatorKind::DropAndReplace { .. } => unreachable!(),
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
            mir::TerminatorKind::Yield { .. } => unreachable!(),
            mir::TerminatorKind::GeneratorDrop => unreachable!(),
            mir::TerminatorKind::FalseEdges { .. } => unreachable!(),
            mir::TerminatorKind::FalseUnwind { .. } => unreachable!(),
        }
    }

    /// block should have one successor in the graph; we jump there
    fn visit_goto(&mut self, target: mir::BasicBlock) {
        debug!("default visit_goto(local: {:?})", target);
        // Propagate the entry condition to the successor block.
        self.current_environment
            .exit_conditions
            .insert(target, self.current_environment.entry_condition.clone());
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
    fn visit_switch_int(
        &mut self,
        discr: &mir::Operand,
        switch_ty: rustc::ty::Ty,
        values: &[u128],
        targets: &[mir::BasicBlock],
    ) {
        debug!(
            "default visit_switch_int(discr: {:?}, switch_ty: {:?}, values: {:?}, targets: {:?})",
            discr, switch_ty, values, targets
        );
        let mut default_exit_condition = self.current_environment.entry_condition.clone();
        let discr = self.visit_operand(discr);
        let discr = discr.as_int_if_known().unwrap_or(discr);
        for i in 0..values.len() {
            let val: AbstractValue = ConstantDomain::U128(values[i]).into();
            let cond = discr.equals(&val, None);
            let not_cond = cond.not(None);
            default_exit_condition = default_exit_condition.and(&not_cond, None);
            let target = targets[i];
            self.current_environment
                .exit_conditions
                .insert(target, cond);
        }
        self.current_environment
            .exit_conditions
            .insert(targets[values.len()], default_exit_condition);
    }

    /// Indicates that the landing pad is finished and unwinding should
    /// continue. Emitted by build::scope::diverge_cleanup.
    fn visit_resume(&self) {
        debug!("default visit_resume()");
    }

    /// Indicates that the landing pad is finished and that the process
    /// should abort. Used to prevent unwinding for foreign items.
    fn visit_abort(&self) {
        debug!("default visit_abort()");
    }

    /// Indicates a normal return. The return place should have been filled in by now.
    fn visit_return(&mut self) {
        debug!("default visit_return()");
        if self.check_for_errors {
            // Done with fixed point, so prepare to summarize.
            let return_guard = self.current_environment.entry_condition.as_bool_if_known();
            if return_guard.unwrap_or(false) {
                self.exit_environment = self.current_environment.clone();
            } else if return_guard.unwrap_or(true) {
                self.exit_environment = self.current_environment.join(
                    &self.exit_environment,
                    &self.current_environment.entry_condition,
                );
            }
        }
    }

    /// Indicates a terminator that can never be reached.
    fn visit_unreachable(&mut self) {
        debug!("default visit_unreachable()");
        // Complain if we are quite sure control gets here.
        if self.check_for_errors
            && self
                .current_environment
                .entry_condition
                .as_bool_if_known()
                .unwrap_or(false)
        {
            //todo: use theorem prover to make sure that the entry condition is not known to be false.
            if self
                .current_environment
                .entry_condition
                .as_bool_if_known()
                .unwrap_or(false)
            {
                let span = self.current_span;
                let mut err = self
                    .session
                    .struct_span_warn(span, "Execution might panic.");
                (self.emit_diagnostic)(&mut err, &mut self.buffered_diagnostics);
            } else {
                self.preconditions.push((
                    self.current_environment
                        .entry_condition
                        .not(Some(self.current_span)),
                    String::from("Execution might panic."),
                ));
            }
        }
    }

    /// Drop the Place
    fn visit_drop(
        &mut self,
        location: &mir::Place,
        target: mir::BasicBlock,
        unwind: Option<mir::BasicBlock>,
    ) {
        debug!(
            "default visit_drop(location: {:?}, target: {:?}, unwind: {:?})",
            location, target, unwind
        );
        // Propagate the entry condition to the successor blocks.
        self.current_environment
            .exit_conditions
            .insert(target, self.current_environment.entry_condition.clone());
        if let Some(unwind_target) = unwind {
            self.current_environment.exit_conditions.insert(
                unwind_target,
                self.current_environment.entry_condition.clone(),
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
    fn visit_call(
        &mut self,
        func: &mir::Operand,
        args: &[mir::Operand],
        destination: &Option<(mir::Place, mir::BasicBlock)>,
        cleanup: Option<mir::BasicBlock>,
        from_hir_call: bool,
    ) {
        debug!("default visit_call(func: {:?}, args: {:?}, destination: {:?}, cleanup: {:?}, from_hir_call: {:?})", func, args, destination, cleanup, from_hir_call);
        let func_to_call = self.visit_operand(func);
        let actual_args: Vec<AbstractValue> =
            args.iter().map(|arg| self.visit_operand(arg)).collect();
        let function_summary = self.get_function_summary(&func_to_call);
        if self.check_for_errors {
            self.check_function_preconditions(&actual_args, &function_summary);
        }
        self.transfer_and_refine_normal_return_state(destination, &actual_args, &function_summary);
        self.transfer_and_refine_cleanup_state(cleanup);
        if self.check_for_errors {
            self.report_calls_to_special_functions(func_to_call, actual_args)
        }
    }

    /// Returns a summary of the function to call, obtained from the summary cache.
    fn get_function_summary(&mut self, func_to_call: &AbstractValue) -> Summary {
        if let Expression::CompileTimeConstant(ConstantDomain::Function {
            def_id: Some(def_id),
            ..
        }) = func_to_call.domain.expression
        {
            self.summary_cache
                .get_summary_for(def_id, Some(self.def_id))
                .clone()
        } else {
            Summary::default()
        }
    }

    /// Checks if the preconditions obtained from the summary of the function being called
    /// are met by the current state and arguments of the calling function.
    /// Preconditions that are definitely false generate diagnostic messages.
    /// Preconditions that are maybe false become preconditions of the calling function.
    fn check_function_preconditions(
        &mut self,
        actual_args: &[AbstractValue],
        function_summary: &Summary,
    ) {
        debug_assert!(self.check_for_errors);
        for (precondition, message) in &function_summary.preconditions {
            let refined_precondition = precondition
                .refine_parameters(actual_args)
                .refine_paths(&mut self.current_environment)
                .refine_with(&self.current_environment.entry_condition, self.current_span);
            if refined_precondition.as_bool_if_known().unwrap_or(false) {
                // The precondition is definitely true.
                continue;
            };
            if !refined_precondition.as_bool_if_known().unwrap_or(true) {
                // The precondition is definitely false, if we ever get to this call site.
                if self
                    .current_environment
                    .entry_condition
                    .as_bool_if_known()
                    .unwrap_or(false)
                {
                    // We always get here if the function is called, and the precondition is always
                    // false, so complain loudly.
                    self.emit_diagnostic_for_precondition(precondition, &message);
                    // Don't promote a false precondition. The callers cannot possibly satisfy it,
                    // so there is no point in complaining at call sites.
                    continue;
                } else {
                    // We might never get here since it depends on the parameter values used to call
                    // this function. If the function is public, let's warn that we might get here.
                    if is_public(self.def_id, &self.tcx) {
                        let warning = format!("possible {}", message.as_str());
                        self.emit_diagnostic_for_precondition(precondition, &warning);
                    } else {
                        // Since the function is not public, we assume that we get to see
                        // every call to this function, so just rely on the inferred precondition.
                    }
                };
                // Fall through and promote the precondition.
                // It does not matter that refined_precondition itself is known to be false,
                // since we add the current entry condition to the promoted precondition.
            }
            // Promote the precondition to a precondition of the current function.
            let promoted_precondition = self
                .current_environment
                .entry_condition
                .not(Some(self.current_span))
                .or(&refined_precondition, Some(self.current_span));
            self.preconditions
                .push((promoted_precondition, message.clone()));
        }
    }

    /// Emit a diagnostic to the effect that the current call might violate a the given precondition
    /// of the called function. Use the provenance of the precondition to point out related locations.
    fn emit_diagnostic_for_precondition(&mut self, precondition: &AbstractValue, diagnostic: &str) {
        // This call is definitely going to be reached
        let span = self.current_span;
        let mut err = self.session.struct_span_warn(span, diagnostic);
        let related_spans: HashSet<&syntax_pos::Span> =
            HashSet::from_iter(precondition.provenance.iter());
        for related_span in related_spans.iter() {
            err.span_note(**related_span, "related location");
        }
        (self.emit_diagnostic)(&mut err, &mut self.buffered_diagnostics);
    }

    /// Updates the current state to reflect the effects of a normal return from the function call.
    fn transfer_and_refine_normal_return_state(
        &mut self,
        destination: &Option<(mir::Place, mir::BasicBlock)>,
        actual_args: &[AbstractValue],
        function_summary: &Summary,
    ) {
        if let Some((place, target)) = destination {
            // Assign function result to place
            let target_path = self.visit_place(place);
            let return_value_path = Path::LocalVariable { ordinal: 0 };
            // Transfer side effects
            self.transfer_and_refine(
                &function_summary.side_effects,
                &target_path,
                return_value_path,
                &actual_args,
            );
            for (i, arg) in actual_args.iter().enumerate() {
                if let AbstractValue {
                    domain:
                        AbstractDomain {
                            expression: Expression::Reference(target_path),
                            ..
                        },
                    ..
                } = arg
                {
                    let parameter_path = Path::LocalVariable { ordinal: i + 1 };
                    self.transfer_and_refine(
                        &function_summary.side_effects,
                        target_path,
                        parameter_path,
                        &actual_args,
                    );
                }
            }
            let mut exit_condition = self.exit_environment.entry_condition.clone();
            if let Some(unwind_condition) = &function_summary.unwind_condition {
                exit_condition =
                    exit_condition.and(&unwind_condition.not(None), Some(self.current_span));
            }
            self.current_environment
                .exit_conditions
                .insert(*target, exit_condition);
        }
    }

    /// Handle the case where the called function does not complete normally.
    fn transfer_and_refine_cleanup_state(&mut self, cleanup: Option<mir::BasicBlock>) {
        if let Some(cleanup_target) = cleanup {
            //todo: transfer and refine the actual cleanup state (once summaries actually include it)
            // this will also require the addition of something like self.current_unwind_environment.
            self.current_environment.exit_conditions.insert(
                cleanup_target,
                self.current_environment.entry_condition.clone(),
            );
        }
    }

    /// If the function being called is a special function like unreachable or panic,
    /// then report a diagnostic if the call is definitely reachable.
    /// If the call might be reached then add a precondition that requires the caller of this
    /// function to ensure that the call to the special function will never be reached at runtime.
    fn report_calls_to_special_functions(
        &mut self,
        func_to_call: AbstractValue,
        actual_args: Vec<AbstractValue>,
    ) {
        debug_assert!(self.check_for_errors);
        let cache = &mut self.constant_value_cache;
        if let Expression::CompileTimeConstant(fun) = func_to_call.domain.expression {
            if cache.check_if_std_intrinsics_unreachable_function(&fun) {
                //todo: use theorem prover to make sure that the entry condition is not known to be false.
                let path_cond = self.current_environment.entry_condition.as_bool_if_known();
                if path_cond.unwrap_or(false) {
                    let span = self.current_span;
                    let mut err = self.session.struct_span_warn(
                        span,
                        "Control reaches a call to std::intrinsics::unreachable.",
                    );
                    (self.emit_diagnostic)(&mut err, &mut self.buffered_diagnostics);
                } else if path_cond.is_none() {
                    self.preconditions.push((
                        self.current_environment
                            .entry_condition
                            .not(Some(self.current_span)),
                        String::from("Control reaches a call to std::intrinsics::unreachable."),
                    ));
                }
            } else if cache.check_if_std_panicking_begin_panic_function(&fun) {
                //todo: use theorem prover to make sure that the entry condition is not known to be false.
                let path_cond = self.current_environment.entry_condition.as_bool_if_known();
                let mut msg = {
                    if let Expression::CompileTimeConstant(ConstantDomain::Str(ref msg)) =
                        actual_args[0].domain.expression
                    {
                        msg.as_str()
                    } else {
                        "Execution might panic."
                    }
                };
                // Since the assertion was conjoined into the entry condition because of the logic
                // of debug_assert!, and this condition was simplified, we cannot distinguish
                // between the case of maybe reaching a definitely false assertion from the case of
                // definitely reaching a maybe false assertion.
                // We therefore report both cases, even though the first would be a candidate for being
                // an inferred precondition, rather than a diagnostic.
                //todo: we need our own library for contract assertions so that we can distinguish
                // such cases.
                if msg.starts_with("assertion failed:") || path_cond.unwrap_or(false) {
                    let msg = msg.replace("assertion failed:", "could not prove assertion:");
                    let span = self.current_span;
                    let mut err = self.session.struct_span_warn(span, &msg);
                    (self.emit_diagnostic)(&mut err, &mut self.buffered_diagnostics);
                } else if path_cond.is_none() {
                    self.preconditions.push((
                        self.current_environment
                            .entry_condition
                            .not(Some(self.current_span)),
                        String::from(msg),
                    ));
                }
            }
        }
    }

    /// Adds a (rpath, rvalue) pair to the current environment for every pair in effects
    /// for which the path is rooted by source_path and where rpath is path re-rooted with
    /// target_path and rvalue is value refined by replacing all occurrences of parameter values
    /// with the corresponding actual values.
    fn transfer_and_refine(
        &mut self,
        effects: &[(Path, AbstractValue)],
        target_path: &Path,
        source_path: Path,
        arguments: &[AbstractValue],
    ) {
        for (path, value) in effects
            .iter()
            .filter(|(p, _)| (*p) == source_path || p.is_rooted_by(&source_path))
        {
            let tpath = path.replace_root(&source_path, target_path.clone());
            let rvalue = value.refine_parameters(arguments);
            self.current_environment.update_value_at(tpath, rvalue);
        }
    }

    /// Jump to the target if the condition has the expected value,
    /// otherwise panic with a message and a cleanup target.
    fn visit_assert(
        &mut self,
        cond: &mir::Operand,
        expected: bool,
        msg: &mir::AssertMessage,
        target: mir::BasicBlock,
        cleanup: Option<mir::BasicBlock>,
    ) {
        debug!("default visit_assert(cond: {:?}, expected: {:?}, msg: {:?}, target: {:?}, cleanup: {:?})", cond, expected, msg, target, cleanup);
        let cond_val = self.visit_operand(cond);
        let not_cond_val = cond_val.not(None);
        // Propagate the entry condition to the successor blocks, conjoined with cond (or !cond).
        let exit_condition = self
            .current_environment
            .entry_condition
            .and(if expected { &cond_val } else { &not_cond_val }, None);
        self.current_environment
            .exit_conditions
            .insert(target, exit_condition);
        if let Some(cleanup_target) = cleanup {
            let cleanup_condition = self
                .current_environment
                .entry_condition
                .and(if expected { &not_cond_val } else { &cond_val }, None);
            self.current_environment
                .exit_conditions
                .insert(cleanup_target, cleanup_condition);
        };
        if self.check_for_errors {
            if let mir::Operand::Constant(..) = cond {
                // Do not complain about compile time constants known to the compiler.
                // Leave that to the compiler.
            } else {
                let cond_as_bool = cond_val.as_bool_if_known();
                if cond_as_bool.is_some() {
                    if expected == cond_as_bool.unwrap() {
                        // If the condition is as expected regardless of whether we can get here or not,
                        // there is nothing to do here.
                        return;
                    }
                    // The condition is not as expected. If we always get here if called, give an error.
                    let entry_cond_as_bool =
                        self.current_environment.entry_condition.as_bool_if_known();
                    if entry_cond_as_bool.is_some() && entry_cond_as_bool.unwrap() {
                        let error = msg.description();
                        let span = self.current_span;
                        let mut error = self.session.struct_span_err(span, error);
                        (self.emit_diagnostic)(&mut error, &mut self.buffered_diagnostics);
                        // No need to push a precondition, the caller can never satisfy it.
                        return;
                    }
                }
                // If we get here, we don't know that this assert is unreachable and we don't know
                // that the condition is as expected, so we need to warn about it somewhere.
                if is_public(self.def_id, &self.tcx) {
                    // We expect public functions to have programmer supplied preconditions
                    // that preclude any assertions from failing. So, if at this stage we get to
                    // complain a bit.
                    let warning = format!("possible {}", msg.description());
                    let span = self.current_span;
                    let mut warning = self.session.struct_span_warn(span, warning.as_str());
                    (self.emit_diagnostic)(&mut warning, &mut self.buffered_diagnostics);
                }
                // Regardless, it is still the caller's problem, so push a precondition.
                let expected_cond = if expected {
                    cond_val
                } else {
                    cond_val.not(Some(self.current_span))
                };
                // To make sure that this assertion never fails, we should either never
                // get here (!entry_condition) or expected_cond should be true.
                let pre_cond = self
                    .current_environment
                    .entry_condition
                    .not(None)
                    .or(&expected_cond, Some(self.current_span));
                self.preconditions
                    .push((pre_cond, String::from(msg.description())));
            }
        };
    }

    /// Calls a specialized visitor for each kind of Rvalue
    fn visit_rvalue(&mut self, path: Path, rvalue: &mir::Rvalue<'tcx>) {
        match rvalue {
            mir::Rvalue::Use(operand) => {
                self.visit_use(path, operand);
            }
            mir::Rvalue::Repeat(operand, count) => {
                self.visit_repeat(path, operand, *count);
            }
            mir::Rvalue::Ref(region, borrow_kind, place) => {
                self.visit_ref(path, region, *borrow_kind, place);
            }
            mir::Rvalue::Len(place) => {
                self.visit_len(path, place);
            }
            mir::Rvalue::Cast(cast_kind, operand, ty) => {
                self.visit_cast(path, *cast_kind, operand, ty);
            }
            mir::Rvalue::BinaryOp(bin_op, left_operand, right_operand) => {
                self.visit_binary_op(path, *bin_op, left_operand, right_operand);
            }
            mir::Rvalue::CheckedBinaryOp(bin_op, left_operand, right_operand) => {
                self.visit_checked_binary_op(path, *bin_op, left_operand, right_operand);
            }
            mir::Rvalue::NullaryOp(null_op, ty) => {
                self.visit_nullary_op(path, *null_op, ty);
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
    fn visit_use(&mut self, path: Path, operand: &mir::Operand) {
        debug!(
            "default visit_use(path: {:?}, operand: {:?})",
            path, operand
        );
        match operand {
            mir::Operand::Copy(place) => {
                self.visit_used_copy(path, place);
            }
            mir::Operand::Move(place) => {
                self.visit_used_move(path, place);
            }
            mir::Operand::Constant(constant) => {
                let mir::Constant {
                    span,
                    ty,
                    user_ty,
                    literal,
                } = constant.borrow();
                let const_value: AbstractValue =
                    self.visit_constant(ty, *user_ty, literal).clone().into();
                self.current_environment
                    .update_value_at(path, const_value.with_provenance(*span));
            }
        };
    }

    /// For each (path', value) pair in the environment where path' is rooted in place,
    /// add a (path'', value) pair to the environment where path'' is a copy of path re-rooted
    /// with place.
    fn visit_used_copy(&mut self, target_path: Path, place: &mir::Place) {
        debug!(
            "default visit_used_copy(target_path: {:?}, place: {:?})",
            target_path, place
        );
        let rpath = self.visit_place(place);
        let rtype = self.get_place_type(place);
        self.copy_or_move_elements(target_path, rpath, rtype, false);
    }

    /// Copies/moves all paths rooted in rpath to corresponding paths rooted in target_path.
    fn copy_or_move_elements(
        &mut self,
        target_path: Path,
        rpath: Path,
        rtype: ExpressionType,
        move_elements: bool,
    ) {
        let mut value_map = self.current_environment.value_map.clone();
        // Some qualified rpaths are patterns that represent collections of values.
        // We need to expand the patterns before doing the actual moves.
        if let Path::QualifiedPath {
            ref qualifier,
            ref selector,
            length,
        } = rpath
        {
            match **selector {
                PathSelector::ConstantIndex {
                    offset, from_end, ..
                } => {
                    let index = if from_end {
                        let len_value = self.get_len((**qualifier).clone());
                        if let AbstractValue {
                            domain:
                                AbstractDomain {
                                    expression:
                                        Expression::CompileTimeConstant(ConstantDomain::U128(len)),
                                    ..
                                },
                            ..
                        } = len_value
                        {
                            len - u128::from(offset)
                        } else {
                            panic!("PathSelector::ConstantIndex implies the length of the value is known")
                        }
                    } else {
                        u128::from(offset)
                    };
                    let index_val = self.constant_value_cache.get_u128_for(index).clone().into();
                    let index_path = Path::QualifiedPath {
                        qualifier: (*qualifier).clone(),
                        selector: box PathSelector::Index(box index_val),
                        length,
                    };
                    self.copy_or_move_elements(
                        target_path,
                        index_path,
                        rtype.clone(),
                        move_elements,
                    );
                    return;
                }
                PathSelector::Subslice { from, to } => {
                    //slice[from:-to] in Python terms.
                    let len = {
                        let len_value = self.get_len((**qualifier).clone());
                        if let AbstractValue {
                            domain:
                                AbstractDomain {
                                    expression:
                                        Expression::CompileTimeConstant(ConstantDomain::U128(len)),
                                    ..
                                },
                            ..
                        } = len_value
                        {
                            u32::try_from(len).unwrap() - to
                        } else {
                            panic!(
                                "PathSelector::Subslice implies the length of the value is known"
                            )
                        }
                    };
                    let slice_value = self.get_new_heap_address();
                    self.current_environment
                        .update_value_at(target_path.clone(), slice_value);
                    for i in from..len {
                        let index_val = self
                            .constant_value_cache
                            .get_u128_for(u128::from(i))
                            .clone()
                            .into();
                        let index_path = Path::QualifiedPath {
                            qualifier: (*qualifier).clone(),
                            selector: box PathSelector::Index(box index_val),
                            length,
                        };
                        let target_index_val = self
                            .constant_value_cache
                            .get_u128_for(u128::try_from(i - from).unwrap())
                            .clone()
                            .into();
                        let indexed_target = Path::QualifiedPath {
                            qualifier: box target_path.clone(),
                            selector: box PathSelector::Index(box target_index_val),
                            length,
                        };
                        self.copy_or_move_elements(
                            indexed_target,
                            index_path,
                            rtype.clone(),
                            move_elements,
                        );
                    }
                    return;
                }
                _ => (),
            }
        };
        // Get here for paths that are not patterns.
        // First look at paths that are rooted in rpath.
        for (path, value) in self
            .current_environment
            .value_map
            .iter()
            .filter(|(p, _)| p.is_rooted_by(&rpath))
        {
            let qualified_path = path.replace_root(&rpath, target_path.clone());
            if move_elements {
                debug!("moving {:?} to {:?}", value, qualified_path);
                value_map = value_map.remove(&path);
            } else {
                debug!("copying {:?} to {:?}", value, qualified_path);
            };
            value_map = value_map.insert(qualified_path, value.with_provenance(self.current_span));
        }
        // Now move (rpath, value) itself.
        let value = self.lookup_path_and_refine_result(rpath.clone(), rtype);
        if move_elements {
            debug!("moving {:?} to {:?}", value, target_path);
            value_map = value_map.remove(&rpath);
        } else {
            debug!("copying {:?} to {:?}", value, target_path);
        };
        value_map = value_map.insert(target_path, value.with_provenance(self.current_span));
        self.current_environment.value_map = value_map;
    }

    /// For each (path', value) pair in the environment where path' is rooted in place,
    /// add a (path'', value) pair to the environment where path'' is a copy of path re-rooted
    /// with place, and also remove the (path', value) pair from the environment.
    fn visit_used_move(&mut self, target_path: Path, place: &mir::Place) {
        debug!(
            "default visit_used_move(target_path: {:?}, place: {:?})",
            target_path, place
        );
        let rpath = self.visit_place(place);
        let rtype = self.get_place_type(place);
        self.copy_or_move_elements(target_path, rpath, rtype, true);
    }

    /// path = [x; 32]
    fn visit_repeat(&mut self, path: Path, operand: &mir::Operand, count: u64) {
        debug!(
            "default visit_repeat(path: {:?}, operand: {:?}, count: {:?})",
            path, operand, count
        );
        self.visit_operand(operand);
        //todo: needs #62
        // get a heap address and put it in Path::AbstractHeapAddress
        // get an abs value for x
        // create a PathSelector::Index paths where the value is the range 0..count
        // add qualified path to the environment with value x.
        self.current_environment
            .update_value_at(path, abstract_value::TOP);
    }

    /// path = &x or &mut x
    fn visit_ref(
        &mut self,
        path: Path,
        region: rustc::ty::Region,
        borrow_kind: mir::BorrowKind,
        place: &mir::Place,
    ) {
        debug!(
            "default visit_ref(path: {:?}, region: {:?}, borrow_kind: {:?}, place: {:?})",
            path, region, borrow_kind, place
        );
        let value_path = self.visit_place(place);
        let value = Expression::Reference(value_path).into();
        self.current_environment.update_value_at(path, value);
    }

    /// path = length of a [X] or [X;n] value.
    fn visit_len(&mut self, path: Path, place: &mir::Place<'tcx>) {
        debug!("default visit_len(path: {:?}, place: {:?})", path, place);
        let place_ty = place.ty(&self.mir.local_decls, self.tcx).to_ty(self.tcx);
        let len_value = if let TyKind::Array(_, len) = place_ty.sty {
            // We only get here if "-Z mir-opt-level=0" was specified.
            // todo: #52 Add a way to run an integration test with a non default compiler option.
            let usize_type = self.tcx.types.usize;
            self.visit_constant(usize_type, None, len).clone().into()
        } else {
            let value_path = self.visit_place(place);
            self.get_len(value_path)
        };
        self.current_environment.update_value_at(path, len_value);
    }

    /// Get the length of an array. Will be a compile time constant if the array length is known.
    fn get_len(&mut self, path: Path) -> AbstractValue {
        let length_path = Path::QualifiedPath {
            length: path.path_length() + 1,
            qualifier: box path,
            selector: box PathSelector::ArrayLength,
        };
        self.lookup_path_and_refine_result(length_path, ExpressionType::Usize)
    }

    /// path = operand. The cast is a no-op for the interpreter.
    fn visit_cast(
        &mut self,
        path: Path,
        cast_kind: mir::CastKind,
        operand: &mir::Operand,
        ty: rustc::ty::Ty,
    ) {
        debug!(
            "default visit_cast(path: {:?}, cast_kind: {:?}, operand: {:?}, ty: {:?})",
            path, cast_kind, operand, ty
        );
        let value = self.visit_operand(operand);
        self.current_environment.update_value_at(path, value);
    }

    /// Apply the given binary operator to the two operands and assign result to path.
    fn visit_binary_op(
        &mut self,
        path: Path,
        bin_op: mir::BinOp,
        left_operand: &mir::Operand,
        right_operand: &mir::Operand,
    ) {
        debug!(
            "default visit_binary_op(path: {:?}, bin_op: {:?}, left_operand: {:?}, right_operand: {:?})",
            path, bin_op, left_operand, right_operand
        );
        let mut left = self.visit_operand(left_operand);
        let mut right = self.visit_operand(right_operand);
        let result = match bin_op {
            mir::BinOp::Add => left.add(&right, Some(self.current_span)),
            mir::BinOp::BitAnd => left.bit_and(&right, Some(self.current_span)),
            mir::BinOp::BitOr => left.bit_or(&right, Some(self.current_span)),
            mir::BinOp::BitXor => left.bit_xor(&right, Some(self.current_span)),
            mir::BinOp::Div => left.div(&right, Some(self.current_span)),
            mir::BinOp::Eq => left.equals(&right, Some(self.current_span)),
            mir::BinOp::Ge => left.ge(&mut right, Some(self.current_span)),
            mir::BinOp::Gt => left.gt(&mut right, Some(self.current_span)),
            mir::BinOp::Le => left.le(&mut right, Some(self.current_span)),
            mir::BinOp::Lt => left.lt(&mut right, Some(self.current_span)),
            mir::BinOp::Mul => left.mul(&right, Some(self.current_span)),
            mir::BinOp::Ne => left.not_equals(&right, Some(self.current_span)),
            mir::BinOp::Offset => left.offset(&right, Some(self.current_span)),
            mir::BinOp::Rem => left.rem(&right, Some(self.current_span)),
            mir::BinOp::Shl => left.shl(&right, Some(self.current_span)),
            mir::BinOp::Shr => left.shr(&right, Some(self.current_span)),
            mir::BinOp::Sub => left.sub(&right, Some(self.current_span)),
        };
        self.current_environment.update_value_at(path, result);
    }

    /// Apply the given binary operator to the two operands, with overflow checking where appropriate
    /// and assign the result to path.
    fn visit_checked_binary_op(
        &mut self,
        path: Path,
        bin_op: mir::BinOp,
        left_operand: &mir::Operand,
        right_operand: &mir::Operand,
    ) {
        debug!("default visit_checked_binary_op(path: {:?}, bin_op: {:?}, left_operand: {:?}, right_operand: {:?})", path, bin_op, left_operand, right_operand);
        // We assume that path is a temporary used to track the operation result and its overflow status.
        let target_type = match path {
            Path::LocalVariable { ordinal } => {
                let loc = &self.mir.local_decls[mir::Local::from(ordinal)];
                match loc.ty.sty {
                    TyKind::Tuple(types) => (&types[0].sty).into(),
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        };
        debug!("target_type = {:?}", target_type);
        let mut left = self.visit_operand(left_operand);
        let mut right = self.visit_operand(right_operand);
        let (result, overflow_flag) = match bin_op {
            mir::BinOp::Add => (
                left.add(&right, Some(self.current_span)),
                left.add_overflows(&mut right, target_type, Some(self.current_span)),
            ),
            mir::BinOp::Mul => (
                left.mul(&right, Some(self.current_span)),
                (&mut left).mul_overflows(&mut right, target_type, Some(self.current_span)),
            ),
            mir::BinOp::Shl => (
                left.shl(&right, Some(self.current_span)),
                left.shl_overflows(&mut right, target_type, Some(self.current_span)),
            ),
            mir::BinOp::Shr => (
                left.shr(&right, Some(self.current_span)),
                left.shr_overflows(&mut right, target_type, Some(self.current_span)),
            ),
            mir::BinOp::Sub => (
                left.sub(&right, Some(self.current_span)),
                left.sub_overflows(&mut right, target_type, Some(self.current_span)),
            ),
            _ => unreachable!(),
        };
        let path0 = Path::QualifiedPath {
            qualifier: box path.clone(),
            selector: box PathSelector::Field(0),
            length: path.path_length() + 1,
        };
        self.current_environment.update_value_at(path0, result);
        let path1 = Path::QualifiedPath {
            qualifier: box path.clone(),
            selector: box PathSelector::Field(1),
            length: path.path_length() + 1,
        };
        self.current_environment
            .update_value_at(path1, overflow_flag);
    }

    /// Create a value based on the given type and assign it to path.
    fn visit_nullary_op(&mut self, path: Path, null_op: mir::NullOp, ty: rustc::ty::Ty) {
        debug!(
            "default visit_nullary_op(path: {:?}, null_op: {:?}, ty: {:?})",
            path, null_op, ty
        );
        let value = match null_op {
            mir::NullOp::Box => self.get_new_heap_address(),
            mir::NullOp::SizeOf => {
                //todo: figure out how to get the size from ty.
                abstract_value::TOP
            }
        };
        self.current_environment.update_value_at(path, value);
    }

    /// Allocates a new heap address and caches it, keyed with the current location
    /// so that subsequent visits deterministically use the same address when processing
    /// the instruction at this location. If we don't do this the fixed point loop wont converge.
    fn get_new_heap_address(&mut self) -> AbstractValue {
        let addresses = &mut self.heap_addresses;
        let constants = &mut self.constant_value_cache;
        addresses
            .entry(self.current_location)
            .or_insert_with(|| constants.get_new_heap_address().into())
            .clone()
    }

    /// Apply the given unary operator to the operand and assign to path.
    fn visit_unary_op(&mut self, path: Path, un_op: mir::UnOp, operand: &mir::Operand) {
        debug!(
            "default visit_unary_op(path: {:?}, un_op: {:?}, operand: {:?})",
            path, un_op, operand
        );
        let operand = self.visit_operand(operand);
        let result = match un_op {
            mir::UnOp::Neg => operand.neg(Some(self.current_span)),
            mir::UnOp::Not => operand.not(Some(self.current_span)),
        };
        self.current_environment.update_value_at(path, result);
    }

    /// Read the discriminant of an ADT and assign to path.
    ///
    /// Undefined (i.e. no effort is made to make it defined, but there’s no reason why it cannot
    /// be defined to return, say, a 0) if ADT is not an enum.
    fn visit_discriminant(&mut self, path: Path, place: &mir::Place) {
        debug!(
            "default visit_discriminant(path: {:?}, place: {:?})",
            path, place
        );
        let adt_path = self.visit_place(place);
        let top = abstract_value::TOP;
        let adt_discriminant_value = self
            .current_environment
            .value_at(&adt_path)
            .unwrap_or(&top)
            .clone();
        self.current_environment
            .update_value_at(path, adt_discriminant_value);
    }

    /// Currently only survives in the MIR that MIRAI sees, if the aggregate is an array.
    /// See https://github.com/rust-lang/rust/issues/48193.
    fn visit_aggregate(
        &mut self,
        path: Path,
        aggregate_kinds: &mir::AggregateKind,
        operands: &[mir::Operand],
    ) {
        debug!(
            "default visit_aggregate(path: {:?}, aggregate_kinds: {:?}, operands: {:?})",
            path, aggregate_kinds, operands
        );
        assert!(match *aggregate_kinds {
            mir::AggregateKind::Array(..) => true,
            _ => false,
        });
        let aggregate_value = self.get_new_heap_address();
        self.current_environment
            .update_value_at(path.clone(), aggregate_value);
        for (i, operand) in operands.iter().enumerate() {
            let index_value = self
                .constant_value_cache
                .get_u128_for(i as u128)
                .clone()
                .into();
            let selector = box PathSelector::Index(box index_value);
            let index_path = Path::QualifiedPath {
                qualifier: box path.clone(),
                selector,
                length: path.path_length() + 1,
            };
            self.visit_used_operand(index_path, operand);
        }
        let length_path = Path::QualifiedPath {
            qualifier: box path.clone(),
            selector: box PathSelector::ArrayLength,
            length: path.path_length() + 1,
        };
        let length_value = self
            .constant_value_cache
            .get_u128_for(operands.len() as u128)
            .clone()
            .into();
        self.current_environment
            .update_value_at(length_path, length_value);
    }

    /// Operand defines the values that can appear inside an rvalue. They are intentionally
    /// limited to prevent rvalues from being nested in one another.
    /// A used operand must move or copy values to a target path.
    fn visit_used_operand(&mut self, target_path: Path, operand: &mir::Operand) {
        match operand {
            mir::Operand::Copy(place) => {
                self.visit_used_copy(target_path, place);
            }
            mir::Operand::Move(place) => {
                self.visit_used_move(target_path, place);
            }
            mir::Operand::Constant(constant) => {
                let mir::Constant {
                    span,
                    ty,
                    user_ty,
                    literal,
                } = constant.borrow();
                let const_value: AbstractValue =
                    self.visit_constant(ty, *user_ty, literal).clone().into();
                self.current_environment
                    .update_value_at(target_path, const_value.with_provenance(*span));
            }
        };
    }

    /// Operand defines the values that can appear inside an rvalue. They are intentionally
    /// limited to prevent rvalues from being nested in one another.
    fn visit_operand(&mut self, operand: &mir::Operand) -> AbstractValue {
        let span = self.current_span;
        let (expression_domain, span) = match operand {
            mir::Operand::Copy(place) => (self.visit_copy(place).domain.expression, span),
            mir::Operand::Move(place) => (self.visit_move(place).domain.expression, span),
            mir::Operand::Constant(constant) => {
                let mir::Constant {
                    span,
                    ty,
                    user_ty,
                    literal,
                } = constant.borrow();
                let const_value = self.visit_constant(ty, *user_ty, literal).clone();
                (Expression::CompileTimeConstant(const_value), *span)
            }
        };
        AbstractValue {
            provenance: vec![span],
            domain: expression_domain.into(),
        }
    }

    /// Copy: The value must be available for use afterwards.
    ///
    /// This implies that the type of the place must be `Copy`; this is true
    /// by construction during build, but also checked by the MIR type checker.
    fn visit_copy(&mut self, place: &mir::Place) -> AbstractValue {
        debug!("default visit_copy(place: {:?})", place);
        let path = self.visit_place(place);
        let place_type = self.get_place_type(place);
        self.lookup_path_and_refine_result(path, place_type)
    }

    /// Move: The value (including old borrows of it) will not be used again.
    ///
    /// Safe for values of all types (modulo future developments towards `?Move`).
    /// Correct usage patterns are enforced by the borrow checker for safe code.
    /// `Copy` may be converted to `Move` to enable "last-use" optimizations.
    fn visit_move(&mut self, place: &mir::Place) -> AbstractValue {
        debug!("default visit_move(place: {:?})", place);
        let path = self.visit_place(place);
        let place_type = self.get_place_type(place);
        self.lookup_path_and_refine_result(path, place_type)
    }

    /// Synthesizes a constant value.
    fn visit_constant(
        &mut self,
        ty: Ty,
        user_ty: Option<UserTypeAnnotationIndex>,
        literal: &LazyConst,
    ) -> &ConstantDomain {
        use rustc::mir::interpret::ConstValue;
        use rustc::mir::interpret::Scalar;
        debug!(
            "default visit_constant(ty: {:?}, user_ty: {:?}, literal: {:?})",
            ty, user_ty, literal
        );
        match literal {
            LazyConst::Evaluated(Const { val, .. }) => {
                debug!("sty: {:?}", ty.sty);
                match ty.sty {
                    TyKind::Bool => match val {
                        ConstValue::Scalar(Scalar::Bits { bits, .. }) => {
                            if *bits == 0 {
                                &ConstantDomain::False
                            } else {
                                &ConstantDomain::True
                            }
                        }
                        _ => unreachable!(),
                    },
                    TyKind::Char => {
                        if let ConstValue::Scalar(Scalar::Bits { bits, .. }) = val {
                            &mut self
                                .constant_value_cache
                                .get_char_for(char::try_from(*bits as u32).unwrap())
                        } else {
                            unreachable!()
                        }
                    }
                    TyKind::Float(..) => match val {
                        ConstValue::Scalar(Scalar::Bits { bits, size }) => match *size {
                            4 => &mut self.constant_value_cache.get_f32_for(*bits as u32),
                            _ => &mut self.constant_value_cache.get_f64_for(*bits as u64),
                        },
                        _ => unreachable!(),
                    },
                    TyKind::FnDef(def_id, ..) => self.visit_function_reference(def_id),
                    TyKind::Int(..) => match val {
                        ConstValue::Scalar(Scalar::Bits { bits, size }) => {
                            let mut value: i128 = match *size {
                                1 => i128::from(*bits as i8),
                                2 => i128::from(*bits as i16),
                                4 => i128::from(*bits as i32),
                                8 => i128::from(*bits as i64),
                                _ => *bits as i128,
                            };
                            &mut self.constant_value_cache.get_i128_for(value)
                        }
                        _ => unreachable!(),
                    },
                    TyKind::Ref(
                        _,
                        &rustc::ty::TyS {
                            sty: TyKind::Str, ..
                        },
                        _,
                    ) => {
                        if let ConstValue::Slice(ptr, len) = val {
                            if let Scalar::Ptr(ptr) = ptr {
                                let alloc = self.tcx.alloc_map.lock().get(ptr.alloc_id);
                                if let Some(mir::interpret::AllocKind::Memory(alloc)) = alloc {
                                    let slice = &alloc.bytes[(ptr.offset.bytes() as usize)..]
                                        [..(*len as usize)];
                                    let s = std::str::from_utf8(slice).expect("non utf8 str");
                                    return &mut self.constant_value_cache.get_string_for(s);
                                } else {
                                    panic!("pointer to erroneous constant {:?}, {:?}", ptr, len)
                                }
                            }
                        };
                        unreachable!()
                    }
                    TyKind::Uint(..) => match val {
                        ConstValue::Scalar(Scalar::Bits { bits, .. }) => {
                            &mut self.constant_value_cache.get_u128_for(*bits)
                        }
                        _ => unreachable!(),
                    },
                    _ => &ConstantDomain::Unimplemented,
                }
            }
            _ => &ConstantDomain::Unimplemented,
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
    fn visit_function_reference(&mut self, def_id: hir::def_id::DefId) -> &ConstantDomain {
        &mut self.constant_value_cache.get_function_constant_for(
            def_id,
            &self.tcx,
            &mut self.summary_cache,
        )
    }

    /// Returns a Path instance that is the essentially the same as the Place instance, but which
    /// can be serialized and used as a cache key.
    fn visit_place(&mut self, place: &mir::Place) -> Path {
        debug!("default visit_place(place: {:?})", place);
        match place {
            mir::Place::Local(local) => Path::LocalVariable {
                ordinal: local.as_usize(),
            },
            mir::Place::Static(boxed_static) => {
                let def_id = boxed_static.def_id;
                let name = summaries::summary_key_str(&self.tcx, def_id);
                Path::StaticVariable {
                    def_id: Some(def_id),
                    summary_cache_key: name,
                }
            }
            mir::Place::Promoted(boxed_promoted) => {
                let index = boxed_promoted.0;
                Path::PromotedConstant {
                    ordinal: index.as_usize(),
                }
            }
            mir::Place::Projection(boxed_place_projection) => {
                let base = self.visit_place(&boxed_place_projection.base);
                let base_type = self.get_place_type(&boxed_place_projection.base);
                let selector = self.visit_projection_elem(&boxed_place_projection.elem);
                if let PathSelector::Deref = selector {
                    // Strip the Deref in order to canonicalize paths
                    let base_val = self.lookup_path_and_refine_result(base.clone(), base_type);
                    return match base_val.domain.expression {
                        Expression::Reference(dereferenced_path) => dereferenced_path,
                        _ => {
                            // If we are dereferencing a path whose value is not known to be a
                            // reference, we just drop the deref so that the path can be found
                            // in the environment.
                            base.clone()
                        }
                    };
                }
                Path::QualifiedPath {
                    length: base.path_length() + 1,
                    qualifier: box base,
                    selector: box selector,
                }
            }
        }
    }

    /// Returns a PathSelector instance that is essentially the same as the ProjectionElem instance
    /// but which can be serialized.
    fn visit_projection_elem(
        &mut self,
        projection_elem: &mir::ProjectionElem<mir::Local, &rustc::ty::TyS>,
    ) -> PathSelector {
        debug!(
            "visit_projection_elem(projection_elem: {:?})",
            projection_elem
        );
        match projection_elem {
            mir::ProjectionElem::Deref => PathSelector::Deref,
            mir::ProjectionElem::Field(field, _) => PathSelector::Field(field.index()),
            mir::ProjectionElem::Index(local) => {
                let local_path = Path::LocalVariable {
                    ordinal: local.as_usize(),
                };
                let index_value =
                    self.lookup_path_and_refine_result(local_path, ExpressionType::Usize);
                PathSelector::Index(box index_value)
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
            mir::ProjectionElem::Subslice { from, to } => PathSelector::Subslice {
                from: *from,
                to: *to,
            },
            mir::ProjectionElem::Downcast(_, index) => PathSelector::Downcast(index.as_usize()),
        }
    }

    /// Returns an ExpressionType value corresponding to the Rustc type of the place.
    fn get_place_type(&mut self, place: &mir::Place) -> ExpressionType {
        (self.get_rustc_place_type(place)).into()
    }

    /// Returns the rustc TyKind of the given place in memory.
    fn get_rustc_place_type(&self, place: &mir::Place<'a>) -> &TyKind<'a> {
        match place {
            mir::Place::Local(local) => {
                let loc = &self.mir.local_decls[mir::Local::from(local.as_usize())];
                &loc.ty.sty
            }
            mir::Place::Static(boxed_static) => &boxed_static.ty.sty,
            mir::Place::Promoted(boxed_promoted) => &boxed_promoted.1.sty,
            mir::Place::Projection(_boxed_place_projection) => {
                self.get_type_for_projection_element(place)
            }
        }
    }

    /// Returns the rustc TyKind of the element selected by projection_elem.
    fn get_type_for_projection_element(&self, place: &mir::Place<'a>) -> &TyKind<'a> {
        if let mir::Place::Projection(boxed_place_projection) = place {
            let base_ty = self.get_rustc_place_type(&boxed_place_projection.base);
            match boxed_place_projection.elem {
                mir::ProjectionElem::Deref => {
                    debug!("base_ty: {:?}", base_ty);
                    match base_ty {
                        TyKind::Adt(..) => base_ty,
                        TyKind::RawPtr(ty_and_mut) => &ty_and_mut.ty.sty,
                        TyKind::Ref(_, ty, _) => &ty.sty,
                        _ => unreachable!(),
                    }
                }
                mir::ProjectionElem::Field(_, ty) => &ty.sty,
                mir::ProjectionElem::Index(_)
                | mir::ProjectionElem::ConstantIndex { .. }
                | mir::ProjectionElem::Subslice { .. } => match base_ty {
                    TyKind::Array(ty, _) => &ty.sty,
                    TyKind::Slice(ty) => &ty.sty,
                    _ => unreachable!(),
                },
                mir::ProjectionElem::Downcast(..) => base_ty,
            }
        } else {
            unreachable!()
        }
    }
}
