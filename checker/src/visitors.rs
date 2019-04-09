// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::abstract_domains::AbstractDomain;
use crate::abstract_value::{self, AbstractValue, Path, PathSelector};
use crate::constant_domain::{ConstantDomain, ConstantValueCache};
use crate::environment::Environment;
use crate::expression::{Expression, ExpressionType};
use crate::k_limits;
use crate::smt_solver::{SmtResult, SmtSolver};
use crate::summaries;
use crate::summaries::{PersistentSummaryCache, Summary};
use crate::utils::{self, is_public};

use log::{debug, info, warn};
use mirai_annotations::{assume, checked_assume, checked_assume_eq, precondition, verify};
use rustc::session::Session;
use rustc::ty::{Ty, TyCtxt, TyKind, UserTypeAnnotationIndex};
use rustc::{hir, mir};
use rustc_data_structures::graph::dominators::Dominators;
use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;
use std::convert::TryInto;
use std::iter::FromIterator;
use std::time::Instant;
use syntax::errors::DiagnosticBuilder;
use syntax_pos;

pub struct MirVisitorCrateContext<'a, 'b: 'a, 'tcx: 'b, E> {
    pub session: &'b Session,
    pub tcx: TyCtxt<'b, 'tcx, 'tcx>,
    pub def_id: hir::def_id::DefId,
    pub mir: &'a mir::Mir<'tcx>,
    pub constant_value_cache: &'a mut ConstantValueCache,
    pub summary_cache: &'a mut PersistentSummaryCache<'b, 'tcx>,
    pub smt_solver: &'a mut dyn SmtSolver<E>,
}

/// Holds the state for the MIR test visitor.
pub struct MirVisitor<'a, 'b: 'a, 'tcx: 'b, E> {
    session: &'b Session,
    tcx: TyCtxt<'b, 'tcx, 'tcx>,
    def_id: hir::def_id::DefId,
    mir: &'a mir::Mir<'tcx>,
    constant_value_cache: &'a mut ConstantValueCache,
    summary_cache: &'a mut PersistentSummaryCache<'b, 'tcx>,
    smt_solver: &'a mut dyn SmtSolver<E>,

    already_report_errors_for_call_to: HashSet<AbstractValue>,
    check_for_errors: bool,
    current_environment: Environment,
    current_location: mir::Location,
    current_span: syntax_pos::Span,
    start_instant: Instant,
    exit_environment: Environment,
    heap_addresses: HashMap<mir::Location, AbstractValue>,
    post_conditions: Vec<AbstractValue>,
    preconditions: Vec<(AbstractValue, String)>,
    unwind_condition: Option<AbstractValue>,
    unwind_environment: Environment,

    pub buffered_diagnostics: Vec<DiagnosticBuilder<'b>>,
}

/// A visitor that simply traverses enough of the MIR associated with a particular code body
/// so that we can test a call to every default implementation of the MirVisitor trait.
impl<'a, 'b: 'a, 'tcx: 'b, E> MirVisitor<'a, 'b, 'tcx, E> {
    pub fn new(
        crate_context: MirVisitorCrateContext<'a, 'b, 'tcx, E>,
    ) -> MirVisitor<'a, 'b, 'tcx, E> {
        MirVisitor {
            session: crate_context.session,
            tcx: crate_context.tcx,
            def_id: crate_context.def_id,
            mir: crate_context.mir,
            constant_value_cache: crate_context.constant_value_cache,
            summary_cache: crate_context.summary_cache,
            smt_solver: crate_context.smt_solver,

            already_report_errors_for_call_to: HashSet::new(),
            check_for_errors: false,
            current_environment: Environment::default(),
            current_location: mir::Location::START,
            current_span: syntax_pos::DUMMY_SP,
            start_instant: Instant::now(),
            exit_environment: Environment::default(),
            heap_addresses: HashMap::default(),
            post_conditions: Vec::new(),
            preconditions: Vec::new(),
            unwind_condition: None,
            unwind_environment: Environment::default(),

            buffered_diagnostics: vec![],
        }
    }

    /// Restores the method only state to its initial state.
    fn reset_visitor_state(&mut self) {
        self.already_report_errors_for_call_to = HashSet::new();
        self.check_for_errors = false;
        self.current_environment = Environment::default();
        self.current_location = mir::Location::START;
        self.current_span = syntax_pos::DUMMY_SP;
        self.start_instant = Instant::now();
        self.exit_environment = Environment::default();
        self.heap_addresses = HashMap::default();
        self.post_conditions = Vec::new();
        self.preconditions = Vec::new();
        self.unwind_condition = None;
        self.unwind_environment = Environment::default();
    }

    fn emit_diagnostic(&mut self, diagnostic_builder: DiagnosticBuilder<'b>) {
        self.buffered_diagnostics.push(diagnostic_builder);
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
        let result =
            if refined_val.is_bottom() {
                // Not found locally, so try statics.
                if let Path::StaticVariable {
                    def_id,
                    ref summary_cache_key,
                    ref expression_type,
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
                    if let Some(result) = &summary.result {
                        let result = result.refine_paths(&mut self.current_environment);
                        if let Expression::AbstractHeapAddress(ordinal) = result.domain.expression {
                            let source_path = Path::LocalVariable { ordinal: 0 };
                            let target_path = &Path::AbstractHeapAddress { ordinal };
                            for (path, value) in summary.side_effects.iter().filter(|(p, _)| {
                                (*p) == source_path || p.is_rooted_by(&source_path)
                            }) {
                                let tpath = path
                                    .replace_root(&source_path, target_path.clone())
                                    .refine_paths(&mut self.current_environment);
                                let rvalue = value.refine_paths(&mut self.current_environment);
                                self.current_environment.update_value_at(tpath, rvalue);
                            }
                        }
                        result
                    } else {
                        Expression::Variable {
                            path: box path.clone(),
                            var_type: expression_type.clone(),
                        }
                        .into()
                    }
                } else if path.path_length() < k_limits::MAX_PATH_LENGTH {
                    if result_type == ExpressionType::Reference {
                        Expression::Reference(path).into()
                    } else {
                        Expression::Variable {
                            path: box path.clone(),
                            var_type: result_type.clone(),
                        }
                        .into()
                    }
                } else {
                    abstract_value::TOP
                }
            } else {
                refined_val
            };
        if result_type == ExpressionType::Bool
            && self.current_environment.entry_condition.implies(&result)
        {
            return abstract_value::TRUE;
        }
        result
    }

    // Path is required to be a temporary used to track an operation result.
    fn get_target_path_type(&mut self, path: &Path) -> ExpressionType {
        match path {
            Path::LocalVariable { ordinal } => {
                let loc = &self.mir.local_decls[mir::Local::from(*ordinal)];
                match loc.ty.sty {
                    TyKind::Tuple(types) => (&types[0].sty).into(),
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
    }

    /// Lookups up the local definition for this ordinal and maps the type information
    /// onto ExpressionType.
    fn get_type_for_local(&self, ordinal: usize) -> ExpressionType {
        let loc = &self.mir.local_decls[mir::Local::from(ordinal)];
        (&loc.ty.sty).into()
    }

    /// Do a topological sort, breaking loops by preferring lower block indices, using dominance
    /// to determine if there is a loop (if a is predecessor of b and b dominates a then they
    /// form a loop and we'll emit the one with the lower index first).
    fn add_predecessors_then_root_block(
        &self,
        root_block: mir::BasicBlock,
        dominators: &Dominators<mir::BasicBlock>,
        block_indices: &mut Vec<mir::BasicBlock>,
        already_added: &mut HashSet<mir::BasicBlock>,
    ) {
        if !already_added.insert(root_block) {
            return;
        }
        let mut added_root = false;
        for pred_bb in self.mir.predecessors_for(root_block).iter() {
            if already_added.contains(pred_bb) {
                continue;
            };
            if !added_root && dominators.is_dominated_by(*pred_bb, root_block) {
                block_indices.push(root_block);
                added_root = true;
            }
            self.add_predecessors_then_root_block(
                *pred_bb,
                dominators,
                block_indices,
                already_added,
            );
        }
        if !added_root {
            block_indices.push(root_block);
        }
    }

    /// Analyze the body and store a summary of its behavior in self.summary_cache.
    /// Returns true if the newly computed summary is different from the summary (if any)
    /// that is already in the cache.
    pub fn visit_body(&mut self, function_name: &str) -> (Option<Summary>, u64) {
        debug!("visit_body({:?}) of {}", self.def_id, function_name);
        let mut elapsed_time_in_seconds = 0;

        // Perform a topological sort on the basic blocks so that blocks are analyzed after their
        // predecessors (except in the case of loop anchors).
        let dominators = self.mir.dominators();

        let mut block_indices = Vec::new();
        let mut already_added = HashSet::new();
        for bb in self.mir.basic_blocks().indices() {
            self.add_predecessors_then_root_block(
                bb,
                &dominators,
                &mut block_indices,
                &mut already_added,
            );
        }

        // in_state[bb] is the join (or widening) of the out_state values of each predecessor of bb
        let mut in_state: HashMap<mir::BasicBlock, Environment> = HashMap::new();
        // out_state[bb] is the environment that results from analyzing block bb, given in_state[bb]
        let mut out_state: HashMap<mir::BasicBlock, Environment> = HashMap::new();
        for bb in block_indices.iter() {
            in_state.insert(*bb, Environment::default());
            out_state.insert(*bb, Environment::default());
        }
        // The entry block has no predecessors and its initial state is the function parameters
        // as well any promoted constants.
        let first_state = self.promote_constants(function_name);

        // Compute a fixed point, which is a value of out_state that will not grow with more iterations.
        let mut changed = true;
        let mut iteration_count = 0;
        while changed {
            changed = false;
            for bb in block_indices.iter() {
                elapsed_time_in_seconds = self.start_instant.elapsed().as_secs();
                if elapsed_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
                    break;
                }

                // Merge output states of predecessors of bb
                let i_state = if bb.index() == 0 {
                    first_state.clone()
                } else {
                    let mut predecessor_states_and_conditions: Vec<(
                        &Environment,
                        Option<&AbstractValue>,
                    )> = self
                        .mir
                        .predecessors_for(*bb)
                        .iter()
                        .map(|pred_bb| {
                            let pred_state = &out_state[pred_bb];
                            let pred_exit_condition = pred_state.exit_conditions.get(bb);
                            (pred_state, pred_exit_condition)
                        })
                        .filter(|(_, pred_exit_condition)| pred_exit_condition.is_some())
                        .collect();
                    if predecessor_states_and_conditions.is_empty() {
                        // nothing is currently known about the predecessors
                        let mut i_state = in_state[bb].clone();
                        i_state.entry_condition = abstract_value::TOP;
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
                            // Once all paths have already been analyzed for a second time (iteration_count == 2)
                            // all blocks not involved in loops will have their final values.
                            // If there are no loops, the next iteration will be a no-op, but since we
                            // don't know if there are loops or not, we do iteration_count == 3 while still
                            // joining. Once we get to iteration_count == 4, we start widening in
                            // order to converge on a fixed point.
                            let mut j_state = if iteration_count < 4 {
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
                // Analyze the basic block
                in_state.insert(*bb, i_state.clone());
                if i_state.entry_condition.as_bool_if_known().unwrap_or(true) {
                    self.current_environment = i_state;
                    self.visit_basic_block(*bb);
                }

                // Check for a fixed point.
                if !self.current_environment.subset(&out_state[bb]) {
                    // There is some path for which self.current_environment.value_at(path) includes
                    // a value this is not present in out_state[bb].value_at(path), so any block
                    // that used out_state[bb] as part of its input state now needs to get reanalyzed.
                    out_state.insert(*bb, self.current_environment.clone());
                    changed = true;
                } else {
                    // If the environment at the end of this block does not have any new values,
                    // we have reached a fixed point for this block.
                    // We update out_state anyway, since exit conditions may have changed.
                    // This is particularly a problem when the current entry is the dummy entry
                    // and the current state is empty except for the exit condition.
                    out_state.get_mut(bb).unwrap().exit_conditions =
                        self.current_environment.exit_conditions.clone();
                }
            }
            if elapsed_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
                break;
            }
            if iteration_count > 50 {
                warn!("fixed point loop diverged in body of {}", function_name);
                break;
            }
            iteration_count += 1;
        }

        // Now traverse the blocks again, doing checks and emitting diagnostics.
        // in_state[bb] is now complete for every basic block bb in the body.
        if iteration_count > 6 {
            warn!(
                "Fixed point loop took {} iterations for {}.",
                iteration_count, function_name
            );
        }
        debug!(
            "Fixed point loop took {} iterations for {}, now checking for errors.",
            iteration_count, function_name
        );
        self.check_for_errors = true;
        for bb in block_indices.iter() {
            let i_state = (&in_state[bb]).clone();
            if i_state.entry_condition.as_bool_if_known().unwrap_or(true) {
                self.current_environment = i_state;
                self.visit_basic_block(*bb);
            }
        }

        // Now create a summary of the body that can be in-lined into call sites.
        let summary = summaries::summarize(
            elapsed_time_in_seconds,
            self.mir.arg_count,
            &self.exit_environment,
            &self.preconditions,
            &self.post_conditions,
            self.unwind_condition.clone(),
            &self.unwind_environment,
        );
        let changed = {
            let old_summary = self.summary_cache.get_summary_for(self.def_id, None);
            summary != *old_summary
        };
        if changed && elapsed_time_in_seconds < k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
            (
                self.summary_cache.set_summary_for(self.def_id, summary),
                elapsed_time_in_seconds,
            )
        } else {
            // Even if the summary has not changed from its previous version, we still
            // update because summary equality ignores provenance (and it does that because
            // we don't have a way to persist provenance across compilations).
            self.summary_cache.set_summary_for(self.def_id, summary);
            (None, elapsed_time_in_seconds)
        }
    }

    /// Use the visitor to compute the state corresponding to promoted constants.
    fn promote_constants(&mut self, function_name: &str) -> Environment {
        let mut state_with_parameters = Environment::default();
        let saved_mir = self.mir;
        let result_root = Path::LocalVariable { ordinal: 0 };
        for (ordinal, constant_mir) in self.mir.promoted.iter().enumerate() {
            self.mir = constant_mir;
            let result_type = self.get_type_for_local(0);
            self.visit_body(function_name);

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
            if self.start_instant.elapsed().as_secs() >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
                return;
            }
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
            mir::StatementKind::InlineAsm(inline_asm) => self.visit_inline_asm(inline_asm),
            mir::StatementKind::Retag(retag_kind, place) => self.visit_retag(*retag_kind, place),
            mir::StatementKind::AscribeUserType(..) => unreachable!(),
            mir::StatementKind::Nop => return,
        }
    }

    /// Write the RHS Rvalue to the LHS Place.
    fn visit_assign(&mut self, place: &mir::Place<'tcx>, rvalue: &mir::Rvalue<'tcx>) {
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
        place: &mir::Place<'tcx>,
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
    fn visit_inline_asm(&mut self, inline_asm: &mir::InlineAsm<'tcx>) {
        debug!("default visit_inline_asm(inline_asm: {:?})", inline_asm);
        if self.check_for_errors {
            let span = self.current_span;
            let err = self.session.struct_span_warn(
                span,
                "Inline assembly code cannot be analyzed by MIRAI. Unsoundly ignoring this.",
            );
            self.emit_diagnostic(err);
        }
    }

    /// Retag references in the given place, ensuring they got fresh tags.  This is
    /// part of the Stacked Borrows model. These statements are currently only interpreted
    /// by miri and only generated when "-Z mir-emit-retag" is passed.
    /// See <https://internals.rust-lang.org/t/stacked-borrows-an-aliasing-model-for-rust/8153/>
    /// for more details.
    fn visit_retag(&self, retag_kind: mir::RetagKind, place: &mir::Place<'tcx>) {
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
    fn visit_terminator(&mut self, source_info: mir::SourceInfo, kind: &mir::TerminatorKind<'tcx>) {
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
        discr: &mir::Operand<'tcx>,
        switch_ty: rustc::ty::Ty<'tcx>,
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
        // An unreachable terminator is the compiler's way to tell us that this block will
        // actually never be reached because the type system says so.
        // Why it is necessary in such a case to actually generate unreachable code is something
        // to ponder, but it is not our concern.
        // We don't have to do anything more here because this block precedes no other block.
    }

    /// Drop the Place
    fn visit_drop(
        &mut self,
        location: &mir::Place<'tcx>,
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
        func: &mir::Operand<'tcx>,
        args: &[mir::Operand<'tcx>],
        destination: &Option<(mir::Place<'tcx>, mir::BasicBlock)>,
        cleanup: Option<mir::BasicBlock>,
        from_hir_call: bool,
    ) {
        debug!("default visit_call(func: {:?}, args: {:?}, destination: {:?}, cleanup: {:?}, from_hir_call: {:?})", func, args, destination, cleanup, from_hir_call);
        let func_to_call = self.visit_operand(func);
        let actual_args: Vec<(Path, AbstractValue)> = args
            .iter()
            .map(|arg| (self.get_operand_path(arg), self.visit_operand(arg)))
            .collect();
        if let Expression::CompileTimeConstant(fun) = &func_to_call.domain.expression {
            if self
                .constant_value_cache
                .check_if_mirai_assume_function(&fun)
            {
                checked_assume!(actual_args.len() == 1);
                self.handle_assume(destination, &actual_args);
                return;
            }
            if self
                .constant_value_cache
                .check_if_mirai_precondition_function(&fun)
            {
                checked_assume!(actual_args.len() == 1);
                self.handle_precondition(&actual_args);
                self.handle_assume(destination, &actual_args);
                return;
            }
            let result: AbstractValue = self.try_to_inline_standard_ops_func(fun, &actual_args);
            if !result.is_bottom() {
                if let Some((place, target)) = destination {
                    let target_path = self.visit_place(place);
                    self.current_environment
                        .update_value_at(target_path, result);
                    let exit_condition = self.exit_environment.entry_condition.clone();
                    self.current_environment
                        .exit_conditions
                        .insert(*target, exit_condition);
                    return;
                }
            }
        }
        let function_summary = self.get_function_summary(&func_to_call);
        if self.check_for_errors
            && !self
                .already_report_errors_for_call_to
                .contains(&func_to_call)
        {
            self.check_function_preconditions(&actual_args, &function_summary, &func_to_call);
        }
        self.transfer_and_refine_normal_return_state(destination, &actual_args, &function_summary);
        self.transfer_and_refine_cleanup_state(cleanup, &actual_args, &function_summary);
        if self.check_for_errors {
            self.report_calls_to_special_functions(func_to_call, &actual_args)
        }
    }

    /// Adds the first and only value in actual_args to the path condition of the destination.
    /// No check is performed, since we get to assume this condition without proof.
    fn handle_assume(
        &mut self,
        destination: &Option<(mir::Place<'tcx>, mir::BasicBlock)>,
        actual_args: &[(Path, AbstractValue)],
    ) {
        precondition!(actual_args.len() == 1);
        let assumed_condition = &actual_args[0].1;
        let exit_condition = self
            .exit_environment
            .entry_condition
            .and(assumed_condition, Some(self.current_span));
        if let Some((_, target)) = destination {
            self.current_environment
                .exit_conditions
                .insert(*target, exit_condition);
        } else {
            unreachable!();
        }
    }

    /// Adds the first and only value in actual_args to the current list of preconditions.
    /// No check is performed, since we get to assume the caller has verified this condition.
    fn handle_precondition(&mut self, actual_args: &[(Path, AbstractValue)]) {
        precondition!(actual_args.len() == 1);
        if self.check_for_errors
            && !self
                .current_environment
                .entry_condition
                .as_bool_if_known()
                .unwrap_or(false)
        {
            let span = self.current_span;
            let warning = self
                .session
                .struct_span_warn(span, "preconditions should be reached unconditionally");
            self.emit_diagnostic(warning);
        }
        let precondition = &actual_args[0].1;
        self.preconditions
            .push((precondition.clone(), "unsatisfied precondition".to_string()));
    }

    /// Standard functions that represent an alternative way to perform operations for which
    /// there are MIR operations should be normalized into the corresponding MIR operations.
    /// In some cases this can be done via a summary, but if not this is the place to do it.
    /// Right now, that means core::slice::len becomes a path with the ArrayLength selector
    /// since there is no way to write a summary to that effect in Rust itself.
    fn try_to_inline_standard_ops_func(
        &mut self,
        fun: &ConstantDomain,
        args: &[(Path, AbstractValue)],
    ) -> AbstractValue {
        if self
            .constant_value_cache
            .check_if_core_slice_len_function(&fun)
        {
            checked_assume!(args.len() == 1);
            let slice_val = &args[0].1;
            let qualifier = match &slice_val.domain.expression {
                Expression::Reference(path) => Some(box path.clone()),
                Expression::Variable { path, .. } => Some(path.clone()),
                Expression::AbstractHeapAddress(ordinal) => {
                    Some(box Path::AbstractHeapAddress { ordinal: *ordinal })
                }
                _ => None,
            };
            if let Some(qualifier) = qualifier {
                let selector = box PathSelector::ArrayLength;
                let len_path = Path::QualifiedPath {
                    length: 2,
                    qualifier,
                    selector,
                };
                return self.lookup_path_and_refine_result(len_path, ExpressionType::Usize);
            }
        }
        abstract_value::BOTTOM
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
        actual_args: &[(Path, AbstractValue)],
        function_summary: &Summary,
        func_to_call: &AbstractValue,
    ) {
        verify!(self.check_for_errors);
        for (precondition, message) in &function_summary.preconditions {
            let refined_precondition = precondition
                .refine_parameters(actual_args)
                .refine_paths(&mut self.current_environment)
                .refine_with(&self.current_environment.entry_condition, self.current_span);
            let (refined_precondition_as_bool, entry_cond_as_bool) =
                self.check_condition_value_and_reachability(&refined_precondition);

            if refined_precondition_as_bool.unwrap_or(false) {
                // The precondition is definitely true.
                continue;
            };
            if !refined_precondition_as_bool.unwrap_or(true)
                || self.preconditions.len() >= k_limits::MAX_INFERRED_PRECONDITIONS
            {
                // The precondition is definitely false, if we ever get to this call site.
                if entry_cond_as_bool.unwrap_or(false)
                    && !refined_precondition_as_bool.unwrap_or(true)
                {
                    // We always get here if the function is called, and the precondition is always
                    // false, so it may seem to make sense to just complain loudly here and not
                    // promote the precondition, which can never be satisfied by the caller.
                    // It could, however, be the case that this function wraps the panic! macro
                    // and that the way to shut MIRAI up about it is to never call it.
                    if is_public(self.def_id, &self.tcx) {
                        // If this is a public function and we assume that calling
                        // panic! is a way of stating a precondition, then we'd also expect a public
                        // caller to have a precondition that prevents us from reaching this call.
                        // So, since we **do** reach this call, complain loudly.
                        if !self
                            .already_report_errors_for_call_to
                            .contains(&func_to_call)
                        {
                            self.emit_diagnostic_for_precondition(precondition, &message);
                            self.already_report_errors_for_call_to
                                .insert(func_to_call.clone());
                        }
                    } else {
                        // Since the function is not public, we assume that we get to see
                        // every call to this function, so just rely on the inferred precondition.
                    }
                } else {
                    // We might never get here since it depends on the parameter values used to call
                    // this function. If the function is public, let's warn that we might get here.
                    if is_public(self.def_id, &self.tcx) {
                        if !self
                            .already_report_errors_for_call_to
                            .contains(&func_to_call)
                        {
                            let warning = format!("possible error: {}", message.as_str());
                            self.emit_diagnostic_for_precondition(precondition, &warning);
                            self.already_report_errors_for_call_to
                                .insert(func_to_call.clone());
                        }
                    } else {
                        // Since the function is not public, we assume that we get to see
                        // every call to this function, so just rely on the inferred precondition.
                    }
                };
                // Fall through and promote the precondition.
                // It does not matter that refined_precondition itself is known to be false,
                // since we add the current entry condition to the promoted precondition.
            }

            if self.preconditions.len() < k_limits::MAX_INFERRED_PRECONDITIONS {
                // Promote the precondition to a precondition of the current function.
                let mut promoted_precondition = self
                    .current_environment
                    .entry_condition
                    .not(None)
                    .or(&refined_precondition, None);
                let mut stacked_provenance = vec![self.current_span];
                stacked_provenance.append(&mut precondition.provenance.clone());
                promoted_precondition.provenance = stacked_provenance;
                self.preconditions
                    .push((promoted_precondition, message.clone()));
            }
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
        self.emit_diagnostic(err);
    }

    /// Updates the current state to reflect the effects of a normal return from the function call.
    fn transfer_and_refine_normal_return_state(
        &mut self,
        destination: &Option<(mir::Place<'tcx>, mir::BasicBlock)>,
        actual_args: &[(Path, AbstractValue)],
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
                actual_args,
            );
            for (i, (target_path, _)) in actual_args.iter().enumerate() {
                let parameter_path = Path::LocalVariable { ordinal: i + 1 };
                self.transfer_and_refine(
                    &function_summary.side_effects,
                    target_path,
                    parameter_path,
                    actual_args,
                );
            }
            let mut exit_condition = self.current_environment.entry_condition.clone();
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
    fn transfer_and_refine_cleanup_state(
        &mut self,
        cleanup: Option<mir::BasicBlock>,
        actual_args: &[(Path, AbstractValue)],
        function_summary: &Summary,
    ) {
        if let Some(cleanup_target) = cleanup {
            for (i, (target_path, _)) in actual_args.iter().enumerate() {
                let parameter_path = Path::LocalVariable { ordinal: i + 1 };
                self.transfer_and_refine(
                    &function_summary.unwind_side_effects,
                    target_path,
                    parameter_path,
                    actual_args,
                );
            }
            let mut exit_condition = self.current_environment.entry_condition.clone();
            if let Some(unwind_condition) = &function_summary.unwind_condition {
                exit_condition = exit_condition.and(&unwind_condition, Some(self.current_span));
            }
            self.current_environment
                .exit_conditions
                .insert(cleanup_target, exit_condition);
        }
    }

    /// If the function being called is a special function like unreachable or panic,
    /// then report a diagnostic if the call is definitely reachable.
    /// If the call might be reached then add a precondition that requires the caller of this
    /// function to ensure that the call to the special function will never be reached at runtime.
    fn report_calls_to_special_functions(
        &mut self,
        func_to_call: AbstractValue,
        actual_args: &[(Path, AbstractValue)],
    ) {
        verify!(self.check_for_errors);
        let cache = &mut self.constant_value_cache;
        if let Expression::CompileTimeConstant(fun) = func_to_call.domain.expression {
            if cache.check_if_mirai_verify_function(&fun) {
                assume!(actual_args.len() == 1); // The type checker ensures this.
                let (_, cond) = &actual_args[0];
                let (cond_as_bool, entry_cond_as_bool) =
                    self.check_condition_value_and_reachability(cond);

                // If we never get here, rather call unreachable!()
                if !entry_cond_as_bool.unwrap_or(true) {
                    let span = self.current_span;
                    let message =
                        "this is unreachable, mark it as such by using the unreachable! macro";
                    let warning = self.session.struct_span_warn(span, message);
                    self.emit_diagnostic(warning);
                    return;
                }

                // If the condition is always true when we get here there is nothing to report.
                if cond_as_bool.unwrap_or(false) {
                    return;
                }

                // If the condition is always false, give an error since that is bad style.
                if !cond_as_bool.unwrap_or(true) {
                    // If the condition is always false, give an error
                    let span = self.current_span;
                    let error = self.session.struct_span_err(span, "false assertion");
                    self.emit_diagnostic(error);
                    if self.preconditions.len() < k_limits::MAX_INFERRED_PRECONDITIONS {
                        // promote the path as precondition. I.e. the program is only correct
                        // if we never get here.
                        self.preconditions.push((
                            self.current_environment
                                .entry_condition
                                .not(None)
                                .replacing_provenance(self.current_span),
                            "will cause a false assertion".to_string(),
                        ));
                    }
                    return;
                }

                // We might get here, or not, and the condition might be false, or not.
                // Give a warning if we don't know all of the callers, or if we run into a k-limit
                if is_public(self.def_id, &self.tcx)
                    || self.preconditions.len() >= k_limits::MAX_INFERRED_PRECONDITIONS
                {
                    // We expect public functions to have programmer supplied preconditions
                    // that preclude any assertions from failing. So, if at this stage we get to
                    // complain a bit.
                    let message = "possibly false assertion";
                    let span = self.current_span;
                    let warning = self.session.struct_span_warn(span, message);
                    self.emit_diagnostic(warning);
                }

                // Now try to push a precondition so that any known or unknown caller of this function
                // is warned that this function will fail if the precondition is not met.
                if self.preconditions.len() < k_limits::MAX_INFERRED_PRECONDITIONS {
                    self.preconditions.push((
                        self.current_environment
                            .entry_condition
                            .not(None)
                            .or(cond, None)
                            .replacing_provenance(self.current_span),
                        "possibly false assertion".to_string(),
                    ));
                }
                return;
            }
            if cache.check_if_std_panicking_begin_panic_function(&fun) {
                let mut path_cond = self.current_environment.entry_condition.as_bool_if_known();
                if path_cond.is_none() {
                    // Try the SMT solver
                    let path_expr = &self.current_environment.entry_condition.domain.expression;
                    let path_smt = self.smt_solver.get_as_smt_predicate(path_expr);
                    if self.smt_solver.solve_expression(&path_smt) == SmtResult::Unsatisfiable {
                        path_cond = Some(false)
                    }
                }
                if !path_cond.unwrap_or(true) {
                    // We never get to this call, so nothing to report.
                    return;
                }

                let msg = if let Expression::CompileTimeConstant(ConstantDomain::Str(ref msg)) =
                    actual_args[0].1.domain.expression
                {
                    if msg.contains("entered unreachable code") {
                        // We treat unreachable!() as an assumption rather than an assertion to prove.
                        return;
                    } else {
                        msg.clone()
                    }
                } else {
                    String::from("execution panic")
                };
                let span = self.current_span;

                if path_cond.unwrap_or(false) && is_public(self.def_id, &self.tcx) {
                    // We always get to this call and we have to assume that the function will
                    // get called, so keep the message certain.
                    let err = self.session.struct_span_warn(span, msg.as_str());
                    self.emit_diagnostic(err);
                } else {
                    // We might get to this call, depending on the state at the call site.
                    //
                    // In the case when an assert macro has been called, the inverse of the assertion
                    // was conjoined into the entry condition and this condition was simplified.
                    // We therefore cannot distinguish between the case of maybe reaching a definitely
                    // false assertion from the case of definitely reaching a maybe false assertion.
                    //
                    // Since the assert and panic macros are commonly used to create preconditions
                    // it would be very inconvenient if this possibly false assertion were reported
                    // as a problem since there would be no way to shut it up. We therefore do not
                    // report this and instead insist that anyone who wants to have MIRAI check
                    // their assertions should use the mirai_annotations::verify! macro instead.
                    //
                    // We **do** have to push a precondition since this is the probable intent.
                    let mut maybe_message = String::from("possible error: ");
                    maybe_message.push_str(msg.as_str());
                    self.preconditions.push((
                        self.current_environment
                            .entry_condition
                            .not(None)
                            .replacing_provenance(self.current_span),
                        maybe_message,
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
        arguments: &[(Path, AbstractValue)],
    ) {
        for (path, value) in effects
            .iter()
            .filter(|(p, _)| (*p) == source_path || p.is_rooted_by(&source_path))
        {
            let tpath = path
                .replace_root(&source_path, target_path.clone())
                .refine_paths(&mut self.current_environment);
            let rvalue = value
                .refine_parameters(arguments)
                .refine_paths(&mut self.current_environment);
            self.current_environment.update_value_at(tpath, rvalue);
        }
    }

    /// Jump to the target if the condition has the expected value,
    /// otherwise panic with a message and a cleanup target.
    fn visit_assert(
        &mut self,
        cond: &mir::Operand<'tcx>,
        expected: bool,
        msg: &mir::AssertMessage<'tcx>,
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
                let (cond_as_bool, entry_cond_as_bool) =
                    self.check_condition_value_and_reachability(&cond_val);

                // Quick exit if things are known.
                if cond_as_bool.is_some() {
                    if expected == cond_as_bool.unwrap() {
                        // If the condition is always as expected when we get here, so there is nothing to report.
                        return;
                    }
                    // If we always get here if called, give an error.
                    if entry_cond_as_bool.is_some() && entry_cond_as_bool.unwrap() {
                        let error = msg.description();
                        let span = self.current_span;
                        let error = self.session.struct_span_err(span, error);
                        self.emit_diagnostic(error);
                        // No need to push a precondition, the caller can never satisfy it.
                        return;
                    }
                }

                // At this point, we don't know that this assert is unreachable and we don't know
                // that the condition is as expected, so we need to warn about it somewhere.
                if is_public(self.def_id, &self.tcx)
                    || self.preconditions.len() >= k_limits::MAX_INFERRED_PRECONDITIONS
                {
                    // We expect public functions to have programmer supplied preconditions
                    // that preclude any assertions from failing. So, if at this stage we get to
                    // complain a bit.
                    let warning = format!("possible {}", msg.description());
                    let span = self.current_span;
                    let warning = self.session.struct_span_warn(span, warning.as_str());
                    self.emit_diagnostic(warning);
                }

                // Regardless, it is still the caller's problem, so push a precondition.
                if self.preconditions.len() < k_limits::MAX_INFERRED_PRECONDITIONS {
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
                        .or(&expected_cond, None)
                        .replacing_provenance(self.current_span);
                    self.preconditions
                        .push((pre_cond, String::from(msg.description())));
                }
            }
        };
    }

    /// Checks the given condition value and also checks if the current entry condition can be true.
    /// If the abstract domains are undecided, resort to using the SMT solver.
    /// Only call this when doing actual error checking, since this is expensive.
    fn check_condition_value_and_reachability(
        &mut self,
        cond_val: &AbstractValue,
    ) -> (Option<bool>, Option<bool>) {
        // Check if the condition is always true (or false) if we get here.
        let mut cond_as_bool = cond_val.as_bool_if_known();
        // Check if we can prove that every call to the current function will reach this call site.
        let mut entry_cond_as_bool = self.current_environment.entry_condition.as_bool_if_known();
        // Use SMT solver if need be.
        if entry_cond_as_bool.is_none() {
            // The abstract domains are unable to decide if the entry condition is always true.
            // (If it could decide that the condition is always false, we wouldn't be here.)
            // See if the SMT solver can prove that the entry condition is always true.
            let smt_expr = {
                let ec = &self.current_environment.entry_condition.domain.expression;
                self.smt_solver.get_as_smt_predicate(ec)
            };
            self.smt_solver.set_backtrack_position();
            self.smt_solver.assert(&smt_expr);
            if self.smt_solver.solve() == SmtResult::Unsatisfiable {
                // The solver can prove that the entry condition is always false.
                entry_cond_as_bool = Some(false);
            }
            if cond_as_bool.is_none() && entry_cond_as_bool.unwrap_or(true) {
                // The abstract domains are unable to decide what the value of cond is.
                cond_as_bool = self.solve_condition(cond_val)
            }
            self.smt_solver.backtrack();
        } else if entry_cond_as_bool.unwrap() && cond_as_bool.is_none() {
            cond_as_bool = self.solve_condition(cond_val)
        }
        (cond_as_bool, entry_cond_as_bool)
    }

    fn solve_condition(&mut self, cond_val: &AbstractValue) -> Option<bool> {
        let ce = &cond_val.domain.expression;
        let cond_smt_expr = self.smt_solver.get_as_smt_predicate(ce);
        match self.smt_solver.solve_expression(&cond_smt_expr) {
            SmtResult::Unsatisfiable => {
                // If we get here, the solver can prove that cond_val is always false.
                Some(false)
            }
            SmtResult::Satisfiable => {
                // We could get here with cond_val being true. Or perhaps not.
                // So lets see if !cond_val is provably false.
                let not_cond_expr = cond_val.not(None).domain.expression;
                let smt_expr = self.smt_solver.get_as_smt_predicate(&not_cond_expr);
                if self.smt_solver.solve_expression(&smt_expr) == SmtResult::Unsatisfiable {
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
    fn visit_use(&mut self, path: Path, operand: &mir::Operand<'tcx>) {
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
                let const_value: AbstractValue = self.visit_constant(ty, *user_ty, &literal.val);
                if let Expression::AbstractHeapAddress(ordinal) = const_value.domain.expression {
                    let rtype = ExpressionType::Reference;
                    let rpath = Path::AbstractHeapAddress { ordinal };
                    self.copy_or_move_elements(path, rpath, rtype, false);
                } else {
                    self.current_environment
                        .update_value_at(path, const_value.with_provenance(*span));
                }
            }
        };
    }

    /// For each (path', value) pair in the environment where path' is rooted in place,
    /// add a (path'', value) pair to the environment where path'' is a copy of path re-rooted
    /// with place.
    fn visit_used_copy(&mut self, target_path: Path, place: &mir::Place<'tcx>) {
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
                            unreachable!("PathSelector::ConstantIndex implies the length of the value is known")
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
                            unreachable!(
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
        let mut value = self.lookup_path_and_refine_result(rpath.clone(), rtype);
        if move_elements {
            debug!("moving {:?} to {:?}", value, target_path);
            value_map = value_map.remove(&rpath);
        } else {
            debug!("copying {:?} to {:?}", value, target_path);
            // if the value is a non primitive and a path reference, update the reference to be the new target
            if let Expression::Variable { var_type, .. } = &value.domain.expression {
                if *var_type == ExpressionType::NonPrimitive {
                    value = AbstractValue {
                        provenance: value.provenance.clone(),
                        domain: Expression::Variable {
                            path: box target_path.clone(),
                            var_type: var_type.clone(),
                        }
                        .into(),
                    };
                }
            }
        }
        value_map = value_map.insert(target_path, value.with_provenance(self.current_span));
        self.current_environment.value_map = value_map;
    }

    /// For each (path', value) pair in the environment where path' is rooted in place,
    /// add a (path'', value) pair to the environment where path'' is a copy of path re-rooted
    /// with place, and also remove the (path', value) pair from the environment.
    fn visit_used_move(&mut self, target_path: Path, place: &mir::Place<'tcx>) {
        debug!(
            "default visit_used_move(target_path: {:?}, place: {:?})",
            target_path, place
        );
        let rpath = self.visit_place(place);
        let rtype = self.get_place_type(place);
        self.copy_or_move_elements(target_path, rpath, rtype, true);
    }

    /// path = [x; 32]
    fn visit_repeat(&mut self, path: Path, operand: &mir::Operand<'tcx>, count: u64) {
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
        region: rustc::ty::Region<'tcx>,
        borrow_kind: mir::BorrowKind,
        place: &mir::Place<'tcx>,
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
        let place_ty = self.get_rustc_place_type(place);
        let len_value = if let TyKind::Array(_, len) = place_ty {
            // We only get here if "-Z mir-opt-level=0" was specified.
            // todo: #52 Add a way to run an integration test with a non default compiler option.
            let usize_type = self.tcx.types.usize;
            self.visit_constant(usize_type, None, &len.val)
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

    /// path = operand as ty.
    fn visit_cast(
        &mut self,
        path: Path,
        cast_kind: mir::CastKind,
        operand: &mir::Operand<'tcx>,
        ty: rustc::ty::Ty<'tcx>,
    ) {
        debug!(
            "default visit_cast(path: {:?}, cast_kind: {:?}, operand: {:?}, ty: {:?})",
            path, cast_kind, operand, ty
        );
        let operand = self.visit_operand(operand);
        let result = if cast_kind == mir::CastKind::Misc {
            operand.cast(ExpressionType::from(&ty.sty))
        } else {
            operand
        };
        self.current_environment.update_value_at(path, result);
    }

    /// Apply the given binary operator to the two operands and assign result to path.
    fn visit_binary_op(
        &mut self,
        path: Path,
        bin_op: mir::BinOp,
        left_operand: &mir::Operand<'tcx>,
        right_operand: &mir::Operand<'tcx>,
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
            mir::BinOp::Ge => left.greater_or_equal(&mut right, Some(self.current_span)),
            mir::BinOp::Gt => left.greater_than(&mut right, Some(self.current_span)),
            mir::BinOp::Le => left.less_or_equal(&mut right, Some(self.current_span)),
            mir::BinOp::Lt => left.less_than(&mut right, Some(self.current_span)),
            mir::BinOp::Mul => left.mul(&right, Some(self.current_span)),
            mir::BinOp::Ne => left.not_equals(&right, Some(self.current_span)),
            mir::BinOp::Offset => left.offset(&right, Some(self.current_span)),
            mir::BinOp::Rem => left.rem(&right, Some(self.current_span)),
            mir::BinOp::Shl => left.shl(&right, Some(self.current_span)),
            mir::BinOp::Shr => {
                // We assume that path is a temporary used to track the operation result.
                let target_type = self.get_target_path_type(&path);
                left.shr(&right, target_type, Some(self.current_span))
            }
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
        left_operand: &mir::Operand<'tcx>,
        right_operand: &mir::Operand<'tcx>,
    ) {
        debug!("default visit_checked_binary_op(path: {:?}, bin_op: {:?}, left_operand: {:?}, right_operand: {:?})", path, bin_op, left_operand, right_operand);
        // We assume that path is a temporary used to track the operation result and its overflow status.
        let target_type = self.get_target_path_type(&path);
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
                left.shr(&right, target_type.clone(), Some(self.current_span)),
                left.shr_overflows(&mut right, target_type, Some(self.current_span)),
            ),
            mir::BinOp::Sub => (
                left.sub(&right, Some(self.current_span)),
                left.sub_overflows(&mut right, target_type, Some(self.current_span)),
            ),
            _ => unreachable!(),
        };
        let path_length = path.path_length();
        assume!(path_length < 1_000_000_000); // We'll run out of memory long before this happens
        let path0 = Path::QualifiedPath {
            qualifier: box path.clone(),
            selector: box PathSelector::Field(0),
            length: path_length + 1,
        };
        self.current_environment.update_value_at(path0, result);
        let path1 = Path::QualifiedPath {
            qualifier: box path.clone(),
            selector: box PathSelector::Field(1),
            length: path_length + 1,
        };
        self.current_environment
            .update_value_at(path1, overflow_flag);
    }

    /// Create a value based on the given type and assign it to path.
    fn visit_nullary_op(&mut self, path: Path, null_op: mir::NullOp, ty: rustc::ty::Ty<'tcx>) {
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
    fn visit_unary_op(&mut self, path: Path, un_op: mir::UnOp, operand: &mir::Operand<'tcx>) {
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
    fn visit_discriminant(&mut self, path: Path, place: &mir::Place<'tcx>) {
        debug!(
            "default visit_discriminant(path: {:?}, place: {:?})",
            path, place
        );
        let adtd_path = self.visit_place(place);
        let adtd_type = self.get_place_type(place);
        let adtd_value = self.lookup_path_and_refine_result(adtd_path, adtd_type);
        self.current_environment.update_value_at(path, adtd_value);
    }

    /// Currently only survives in the MIR that MIRAI sees, if the aggregate is an array.
    /// See https://github.com/rust-lang/rust/issues/48193.
    fn visit_aggregate(
        &mut self,
        path: Path,
        aggregate_kinds: &mir::AggregateKind<'tcx>,
        operands: &[mir::Operand<'tcx>],
    ) {
        debug!(
            "default visit_aggregate(path: {:?}, aggregate_kinds: {:?}, operands: {:?})",
            path, aggregate_kinds, operands
        );
        checked_assume!(match *aggregate_kinds {
            mir::AggregateKind::Array(..) => true,
            _ => false,
        });
        if path.path_length() >= k_limits::MAX_PATH_LENGTH {
            // If we get to this limit we have a very weird array. Just use Top.
            self.current_environment
                .update_value_at(path, abstract_value::TOP);
            return;
        }
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
    fn visit_used_operand(&mut self, target_path: Path, operand: &mir::Operand<'tcx>) {
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
                let const_value: AbstractValue = self.visit_constant(ty, *user_ty, &literal.val);
                self.current_environment
                    .update_value_at(target_path, const_value.with_provenance(*span));
            }
        };
    }

    /// Returns the path (location/lh-value) of the given operand.
    fn get_operand_path(&mut self, operand: &mir::Operand<'tcx>) -> Path {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => self.visit_place(place),
            mir::Operand::Constant(..) => Path::Constant {
                value: box self.visit_operand(operand),
            },
        }
    }

    /// Operand defines the values that can appear inside an rvalue. They are intentionally
    /// limited to prevent rvalues from being nested in one another.
    fn visit_operand(&mut self, operand: &mir::Operand<'tcx>) -> AbstractValue {
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
                let const_value = self.visit_constant(ty, *user_ty, &literal.val);
                (const_value.domain.expression, *span)
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
    fn visit_copy(&mut self, place: &mir::Place<'tcx>) -> AbstractValue {
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
    fn visit_move(&mut self, place: &mir::Place<'tcx>) -> AbstractValue {
        debug!("default visit_move(place: {:?})", place);
        let path = self.visit_place(place);
        let place_type = self.get_place_type(place);
        self.lookup_path_and_refine_result(path, place_type)
    }

    /// Synthesizes a constant value.
    fn visit_constant(
        &mut self,
        ty: Ty<'tcx>,
        user_ty: Option<UserTypeAnnotationIndex>,
        literal: &mir::interpret::ConstValue<'tcx>,
    ) -> AbstractValue {
        use rustc::mir::interpret::{AllocKind, Scalar};
        debug!(
            "default visit_constant(ty: {:?}, user_ty: {:?}, literal: {:?})",
            ty, user_ty, literal
        );
        match literal {
            mir::interpret::ConstValue::Unevaluated(def_id, ..) => {
                let name = utils::summary_key_str(&self.tcx, *def_id);
                let expression_type: ExpressionType = ExpressionType::from(&ty.sty);
                let path = Path::StaticVariable {
                    def_id: Some(*def_id),
                    summary_cache_key: name,
                    expression_type: expression_type.clone(),
                };
                self.lookup_path_and_refine_result(path, expression_type)
            }
            _ => {
                let result;
                match ty.sty {
                    TyKind::Bool => {
                        result = match literal {
                            mir::interpret::ConstValue::Scalar(Scalar::Bits { bits, .. }) => {
                                if *bits == 0 {
                                    &ConstantDomain::False
                                } else {
                                    &ConstantDomain::True
                                }
                            }
                            _ => unreachable!(),
                        };
                    }
                    TyKind::Char => {
                        result = if let mir::interpret::ConstValue::Scalar(Scalar::Bits {
                            bits,
                            ..
                        }) = literal
                        {
                            &mut self
                                .constant_value_cache
                                .get_char_for(char::try_from(*bits as u32).unwrap())
                        } else {
                            unreachable!()
                        };
                    }
                    TyKind::Float(..) => {
                        result = match literal {
                            mir::interpret::ConstValue::Scalar(Scalar::Bits { bits, size }) => {
                                match *size {
                                    4 => &mut self.constant_value_cache.get_f32_for(*bits as u32),
                                    _ => &mut self.constant_value_cache.get_f64_for(*bits as u64),
                                }
                            }
                            _ => unreachable!(),
                        };
                    }
                    TyKind::FnDef(def_id, ..) => {
                        result = self.visit_function_reference(def_id);
                    }
                    TyKind::Int(..) => {
                        result = match literal {
                            mir::interpret::ConstValue::Scalar(Scalar::Bits { bits, size }) => {
                                let value: i128 = match *size {
                                    1 => i128::from(*bits as i8),
                                    2 => i128::from(*bits as i16),
                                    4 => i128::from(*bits as i32),
                                    8 => i128::from(*bits as i64),
                                    _ => *bits as i128,
                                };
                                &mut self.constant_value_cache.get_i128_for(value)
                            }
                            _ => unreachable!(),
                        };
                    }
                    TyKind::Ref(
                        _,
                        &rustc::ty::TyS {
                            sty: TyKind::Str, ..
                        },
                        _,
                    ) => {
                        result = if let mir::interpret::ConstValue::Slice(ptr, len) = literal {
                            if let Scalar::Ptr(ptr) = ptr {
                                let alloc = self.tcx.alloc_map.lock().get(ptr.alloc_id);
                                if let Some(AllocKind::Memory(alloc)) = alloc {
                                    let slice = &alloc.bytes[(ptr.offset.bytes() as usize)..]
                                        [..(*len as usize)];
                                    let s = std::str::from_utf8(slice).expect("non utf8 str");
                                    &mut self.constant_value_cache.get_string_for(s)
                                } else {
                                    panic!("pointer to erroneous constant {:?}, {:?}", ptr, len);
                                }
                            } else {
                                unimplemented!(
                                    "unsupported mir::interpret::ConstValue::Slice(ptr, ..): {:?}",
                                    ptr
                                );
                            }
                        } else {
                            unimplemented!("unsupported val of type Ref: {:?}", literal);
                        };
                    }
                    TyKind::Ref(
                        _,
                        &rustc::ty::TyS {
                            sty: TyKind::Array(elem_type, length),
                            ..
                        },
                        _,
                    ) => {
                        if let mir::interpret::ConstValue::Scalar(Scalar::Bits { bits, .. }, ..) =
                            &length.val
                        {
                            let len = *bits;
                            if let mir::interpret::ConstValue::Scalar(sc) = literal {
                                if let Scalar::Ptr(ptr) = sc {
                                    let alloc = self.tcx.alloc_map.lock().get(ptr.alloc_id);
                                    if let Some(AllocKind::Memory(alloc)) = alloc {
                                        let e_type = ExpressionType::from(&elem_type.sty);
                                        if e_type != ExpressionType::U8 {
                                            info!(
                                                "Untested case of mir::interpret::ConstValue::Scalar found at {:?}",
                                                self.current_span
                                            );
                                        }
                                        return self.deconstruct_constant_array(
                                            &alloc.bytes,
                                            e_type,
                                            Some(len),
                                        );
                                    } else {
                                        unimplemented!(
                                            "unsupported alloc_id {:?} returned: {:?}",
                                            ptr.alloc_id,
                                            alloc
                                        );
                                    }
                                } else {
                                    unimplemented!("unsupported Scalar: {:?}", sc);
                                }
                            } else {
                                unimplemented!("unsupported constant value: {:?}", literal);
                            }
                        } else {
                            unimplemented!("unsupported array length: {:?}", length);
                        };
                    }
                    TyKind::Ref(
                        _,
                        &rustc::ty::TyS {
                            sty: TyKind::Slice(elem_type),
                            ..
                        },
                        _,
                    ) => {
                        if let mir::interpret::ConstValue::Slice(ptr, len) = literal {
                            if let Scalar::Ptr(ptr) = ptr {
                                let alloc = self.tcx.alloc_map.lock().get(ptr.alloc_id);
                                if let Some(AllocKind::Memory(alloc)) = alloc {
                                    let e_type = ExpressionType::from(&elem_type.sty);
                                    return self.deconstruct_constant_array(
                                        &alloc.bytes,
                                        e_type,
                                        None,
                                    );
                                } else {
                                    panic!("pointer to erroneous constant {:?}, {:?}", ptr, len);
                                }
                            } else {
                                unimplemented!(
                                    "unsupported mir::interpret::ConstValue::Slice(ptr, ..): {:?}",
                                    ptr
                                );
                            }
                        } else {
                            unimplemented!("unsupported val of type Ref: {:?}", literal);
                        };
                    }
                    TyKind::Uint(..) => {
                        result = match literal {
                            mir::interpret::ConstValue::Scalar(Scalar::Bits { bits, .. }) => {
                                &mut self.constant_value_cache.get_u128_for(*bits)
                            }
                            _ => unreachable!(),
                        };
                    }
                    _ => {
                        println!("span: {:?}", self.current_span);
                        println!("unimplemented constant {:?}", literal);
                        result = &ConstantDomain::Unimplemented;
                    }
                };
                result.clone().into()
            }
        }
    }

    /// Deserializes the given bytes into a constant array of the given element type and then
    /// stores the array elements in the environment with a path for each element, rooted
    /// in a new abstract heap address that represents the array itself and which is returned
    /// as the result of this function. The caller should then copy the path tree to the target
    /// root known to the caller. Since the array is a compile time constant, there is no storage
    /// that needs to get freed or moved.
    ///
    /// The optional length is available as a separate compile time constant in the case of byte string
    /// constants. It is passed in here to check against the length of the bytes array as a safety check.
    fn deconstruct_constant_array(
        &mut self,
        bytes: &[u8],
        elem_type: ExpressionType,
        len: Option<u128>,
    ) -> AbstractValue {
        let array_value = self.get_new_heap_address();
        let ordinal =
            if let Expression::AbstractHeapAddress(ordinal) = array_value.domain.expression {
                ordinal
            } else {
                unreachable!()
            };
        let array_path = Path::AbstractHeapAddress { ordinal };
        let mut last_index: u128 = 0;
        for (i, operand) in self
            .get_element_values(bytes, elem_type, len)
            .into_iter()
            .enumerate()
        {
            last_index = i as u128;
            let index_value = self
                .constant_value_cache
                .get_u128_for(last_index)
                .clone()
                .into();
            let selector = box PathSelector::Index(box index_value);
            let index_path = Path::QualifiedPath {
                qualifier: box array_path.clone(),
                selector,
                length: array_path.path_length() + 1,
            };
            self.current_environment
                .update_value_at(index_path, operand);
        }
        let length_path = Path::QualifiedPath {
            qualifier: box array_path.clone(),
            selector: box PathSelector::ArrayLength,
            length: array_path.path_length() + 1,
        };
        let length_value = self
            .constant_value_cache
            .get_u128_for(last_index + 1)
            .clone()
            .into();
        self.current_environment
            .update_value_at(length_path, length_value);
        array_value
    }

    /// A helper for deconstruct_constant_array. See its comments.
    /// This does the deserialization part, whereas deconstruct_constant_array does the environment
    /// updates.
    fn get_element_values(
        &mut self,
        bytes: &[u8],
        elem_type: ExpressionType,
        len: Option<u128>,
    ) -> Vec<AbstractValue> {
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
                    _ => unreachable!(),
                }
            }

            let signed_numbers = chunks.map(get_signed_element_value);
            signed_numbers
                .map(|n| ConstantDomain::I128(n).into())
                .collect()
        } else {
            fn get_unsigned_element_value(bytes: &[u8]) -> u128 {
                match bytes.len() {
                    1 => u128::from(bytes[0]),
                    2 => u128::from(u16::from_ne_bytes(bytes.try_into().unwrap())),
                    4 => u128::from(u32::from_ne_bytes(bytes.try_into().unwrap())),
                    8 => u128::from(u64::from_ne_bytes(bytes.try_into().unwrap())),
                    16 => u128::from_ne_bytes(bytes.try_into().unwrap()),
                    _ => unreachable!(),
                }
            }

            let unsigned_numbers = chunks.map(get_unsigned_element_value);
            unsigned_numbers
                .map(|n| ConstantDomain::U128(n).into())
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
    fn visit_function_reference(&mut self, def_id: hir::def_id::DefId) -> &ConstantDomain {
        &mut self.constant_value_cache.get_function_constant_for(
            def_id,
            &self.tcx,
            &mut self.summary_cache,
        )
    }

    /// Returns a Path instance that is the essentially the same as the Place instance, but which
    /// can be serialized and used as a cache key.
    fn visit_place(&mut self, place: &mir::Place<'tcx>) -> Path {
        debug!("default visit_place(place: {:?})", place);
        match place {
            mir::Place::Base(base_place) => match base_place {
                mir::PlaceBase::Local(local) => Path::LocalVariable {
                    ordinal: local.as_usize(),
                },
                mir::PlaceBase::Static(boxed_static) => match boxed_static.kind {
                    mir::StaticKind::Promoted(promoted) => {
                        let index = promoted.index();
                        Path::PromotedConstant { ordinal: index }
                    }
                    mir::StaticKind::Static(def_id) => {
                        let name = utils::summary_key_str(&self.tcx, def_id);
                        Path::StaticVariable {
                            def_id: Some(def_id),
                            summary_cache_key: name,
                            expression_type: self.get_place_type(place),
                        }
                    }
                },
            },
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
                let base_path_length = base.path_length();
                checked_assume!(base_path_length < std::usize::MAX);
                Path::QualifiedPath {
                    length: base_path_length + 1,
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
        projection_elem: &mir::ProjectionElem<mir::Local, &rustc::ty::TyS<'tcx>>,
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
    fn get_place_type(&mut self, place: &mir::Place<'tcx>) -> ExpressionType {
        (self.get_rustc_place_type(place)).into()
    }

    /// Returns the rustc TyKind of the given place in memory.
    fn get_rustc_place_type(&self, place: &mir::Place<'tcx>) -> &'tcx TyKind<'tcx> {
        match place {
            mir::Place::Base(base_place) => match base_place {
                mir::PlaceBase::Local(local) => {
                    let loc = &self.mir.local_decls[mir::Local::from(local.as_usize())];
                    &loc.ty.sty
                }
                mir::PlaceBase::Static(boxed_static) => &boxed_static.ty.sty,
            },
            mir::Place::Projection(_boxed_place_projection) => {
                self.get_type_for_projection_element(place)
            }
        }
    }

    /// Returns the rustc TyKind of the element selected by projection_elem.
    fn get_type_for_projection_element(&self, place: &mir::Place<'tcx>) -> &'tcx TyKind<'tcx> {
        if let mir::Place::Projection(boxed_place_projection) = place {
            let base_ty = self.get_rustc_place_type(&boxed_place_projection.base);
            match boxed_place_projection.elem {
                mir::ProjectionElem::Deref => match base_ty {
                    TyKind::Adt(..) => base_ty,
                    TyKind::RawPtr(ty_and_mut) => &ty_and_mut.ty.sty,
                    TyKind::Ref(_, ty, _) => &ty.sty,
                    _ => unreachable!(
                        "span: {:?}\nelem: {:?}",
                        self.current_span, boxed_place_projection.elem
                    ),
                },
                mir::ProjectionElem::Field(_, ty) => &ty.sty,
                mir::ProjectionElem::Index(_)
                | mir::ProjectionElem::ConstantIndex { .. }
                | mir::ProjectionElem::Subslice { .. } => match base_ty {
                    TyKind::Adt(..) => base_ty,
                    TyKind::Array(ty, _) => &ty.sty,
                    TyKind::Slice(ty) => &ty.sty,
                    _ => unreachable!(
                        "span: {:?}\nelem: {:?}",
                        self.current_span, boxed_place_projection.elem
                    ),
                },
                mir::ProjectionElem::Downcast(..) => base_ty,
            }
        } else {
            unreachable!("span: {:?}\nplace: {:?}", self.current_span, place)
        }
    }
}
