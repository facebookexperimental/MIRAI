// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::abstract_value;
use crate::abstract_value::AbstractValue;
use crate::abstract_value::AbstractValueTrait;
use crate::constant_domain::{ConstantDomain, ConstantValueCache, KnownFunctionNames};
use crate::environment::Environment;
use crate::expression::{Expression, ExpressionType};
use crate::k_limits;
use crate::path::PathRefinement;
use crate::path::{Path, PathEnum, PathSelector};
use crate::smt_solver::{SmtResult, SmtSolver};
use crate::summaries;
use crate::summaries::{PersistentSummaryCache, Precondition, Summary};
use crate::utils::{self, is_public};

use log_derive::logfn_inputs;
use mirai_annotations::{assume, checked_assume, checked_assume_eq, precondition, verify};
use rustc::session::Session;
use rustc::ty::subst::SubstsRef;
use rustc::ty::{AdtDef, Ty, TyCtxt, TyKind, UserTypeAnnotationIndex};
use rustc::{hir, mir};
use rustc_data_structures::graph::dominators::Dominators;
use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;
use std::convert::TryInto;
use std::fmt::{Debug, Formatter, Result};
use std::rc::Rc;
use std::time::Instant;
use syntax::errors::DiagnosticBuilder;
use syntax_pos;

pub struct MirVisitorCrateContext<'a, 'b, 'tcx, E> {
    pub session: &'b Session,
    pub tcx: &'b TyCtxt<'tcx>,
    pub def_id: hir::def_id::DefId,
    pub mir: &'a mir::Body<'tcx>,
    pub constant_value_cache: &'a mut ConstantValueCache<'tcx>,
    pub summary_cache: &'a mut PersistentSummaryCache<'b, 'tcx>,
    pub smt_solver: &'a mut dyn SmtSolver<E>,
    pub buffered_diagnostics: &'a mut Vec<DiagnosticBuilder<'b>>,
    pub outer_fixed_point_iteration: usize,
}

impl<'a, 'b: 'a, 'tcx: 'b, E> Debug for MirVisitorCrateContext<'a, 'b, 'tcx, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "MirVisitorCrateContext".fmt(f)
    }
}

/// Holds the state for the MIR test visitor.
pub struct MirVisitor<'a, 'b, 'tcx, E> {
    session: &'b Session,
    tcx: &'b TyCtxt<'tcx>,
    def_id: hir::def_id::DefId,
    mir: &'a mir::Body<'tcx>,
    constant_value_cache: &'a mut ConstantValueCache<'tcx>,
    summary_cache: &'a mut PersistentSummaryCache<'b, 'tcx>,
    smt_solver: &'a mut dyn SmtSolver<E>,
    buffered_diagnostics: &'a mut Vec<DiagnosticBuilder<'b>>,
    outer_fixed_point_iteration: usize,

    already_report_errors_for_call_to: HashSet<Rc<AbstractValue>>,
    check_for_errors: bool,
    check_for_unconditional_precondition: bool,
    current_environment: Environment,
    current_location: mir::Location,
    current_span: syntax_pos::Span,
    start_instant: Instant,
    exit_environment: Environment,
    heap_addresses: HashMap<mir::Location, Rc<AbstractValue>>,
    post_condition: Option<Rc<AbstractValue>>,
    preconditions: Vec<Precondition>,
    unwind_condition: Option<Rc<AbstractValue>>,
    unwind_environment: Environment,
    fresh_variable_offset: usize,
}

impl<'a, 'b: 'a, 'tcx: 'b, E> Debug for MirVisitor<'a, 'b, 'tcx, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "MirVisitor".fmt(f)
    }
}

/// A visitor that simply traverses enough of the MIR associated with a particular code body
/// so that we can test a call to every default implementation of the MirVisitor trait.
impl<'a, 'b: 'a, 'tcx: 'b, E> MirVisitor<'a, 'b, 'tcx, E> {
    #[logfn_inputs(TRACE)]
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
            buffered_diagnostics: crate_context.buffered_diagnostics,
            outer_fixed_point_iteration: crate_context.outer_fixed_point_iteration,

            already_report_errors_for_call_to: HashSet::new(),
            check_for_errors: false,
            check_for_unconditional_precondition: true,
            current_environment: Environment::default(),
            current_location: mir::Location::START,
            current_span: syntax_pos::DUMMY_SP,
            start_instant: Instant::now(),
            exit_environment: Environment::default(),
            heap_addresses: HashMap::default(),
            post_condition: None,
            preconditions: Vec::new(),
            unwind_condition: None,
            unwind_environment: Environment::default(),
            fresh_variable_offset: 0,
        }
    }

    /// Restores the method only state to its initial state.
    #[logfn_inputs(TRACE)]
    fn reset_visitor_state(&mut self) {
        self.already_report_errors_for_call_to = HashSet::new();
        self.check_for_errors = false;
        self.check_for_unconditional_precondition = true;
        self.current_environment = Environment::default();
        self.current_location = mir::Location::START;
        self.current_span = syntax_pos::DUMMY_SP;
        self.start_instant = Instant::now();
        self.exit_environment = Environment::default();
        self.heap_addresses = HashMap::default();
        self.post_condition = None;
        self.preconditions = Vec::new();
        self.unwind_condition = None;
        self.unwind_environment = Environment::default();
        self.fresh_variable_offset = 1000;
    }

    #[logfn_inputs(TRACE)]
    fn emit_diagnostic(&mut self, diagnostic_builder: DiagnosticBuilder<'b>) {
        self.buffered_diagnostics.push(diagnostic_builder);
    }

    /// Use the local and global environments to resolve Path to an abstract value.
    /// For now, promoted constants just return Top.
    #[logfn_inputs(TRACE)]
    fn lookup_path_and_refine_result(
        &mut self,
        path: Rc<Path>,
        result_type: ExpressionType,
    ) -> Rc<AbstractValue> {
        if let PathEnum::Constant { value } = &path.value {
            return value.clone();
        }
        let refined_val = {
            let bottom = abstract_value::BOTTOM.into();
            let local_val = self
                .current_environment
                .value_at(&path)
                .unwrap_or(&bottom)
                .clone();
            if self
                .current_environment
                .entry_condition
                .as_bool_if_known()
                .is_none()
            {
                local_val.refine_with(&self.current_environment.entry_condition, 0)
            } else {
                local_val
            }
        };
        let result = if refined_val.is_bottom() {
            // Not found locally, so try statics.
            if let PathEnum::StaticVariable {
                def_id,
                ref summary_cache_key,
                ref expression_type,
            } = &path.value
            {
                let summary;
                let summary = if let Some(def_id) = def_id {
                    self.summary_cache
                        .get_summary_for(*def_id, Some(self.def_id))
                } else {
                    summary = self
                        .summary_cache
                        .get_persistent_summary_for(summary_cache_key);
                    &summary
                };
                if let Some(result) = &summary.result {
                    let result = result.refine_paths(&self.current_environment);
                    if let Expression::AbstractHeapAddress(ordinal) = result.expression {
                        let source_path = Rc::new(PathEnum::LocalVariable { ordinal: 0 }.into());
                        let target_path: Rc<Path> =
                            Rc::new(PathEnum::AbstractHeapAddress { ordinal }.into());
                        for (path, value) in summary
                            .side_effects
                            .iter()
                            .filter(|(p, _)| (*p) == source_path || p.is_rooted_by(&source_path))
                        {
                            let tpath = Rc::new(path.clone())
                                .replace_root(&source_path, target_path.clone())
                                .refine_paths(&self.current_environment);
                            let rvalue = value.refine_paths(&self.current_environment);
                            self.current_environment.update_value_at(tpath, rvalue);
                        }
                    }
                    result
                } else {
                    let result = AbstractValue::make_from(
                        Expression::Variable {
                            path: path.clone(),
                            var_type: expression_type.clone(),
                        },
                        1,
                    );
                    self.current_environment
                        .update_value_at(path, result.clone());
                    result
                }
            } else if path.path_length() < k_limits::MAX_PATH_LENGTH {
                let result = if result_type == ExpressionType::Reference {
                    AbstractValue::make_from(Expression::Reference(path.clone()), 1)
                } else {
                    AbstractValue::make_from(
                        Expression::Variable {
                            path: path.clone(),
                            var_type: result_type.clone(),
                        },
                        1,
                    )
                };
                self.current_environment
                    .update_value_at(path, result.clone());
                result
            } else {
                Rc::new(abstract_value::TOP)
            }
        } else {
            refined_val
        };
        if result_type == ExpressionType::Bool
            && self.current_environment.entry_condition.implies(&result)
        {
            return Rc::new(abstract_value::TRUE);
        }
        result
    }

    // Path is required to be rooted in a temporary used to track a checked operation result.
    // The result type of the local will be a tuple (t, bool).
    // The result of this function is the t part.
    #[logfn_inputs(TRACE)]
    fn get_first_part_of_target_path_type_tuple(&mut self, path: &Rc<Path>) -> ExpressionType {
        match self.get_path_rustc_type(path) {
            TyKind::Tuple(types) => (&types[0].expect_ty().sty).into(),
            _ => unreachable!(),
        }
    }

    // Path is required to be rooted in a temporary used to track an operation result.
    #[logfn_inputs(TRACE)]
    fn get_target_path_type(&mut self, path: &Rc<Path>) -> ExpressionType {
        self.get_path_rustc_type(path).into()
    }

    /// Lookups up the local definition for this ordinal and maps the type information
    /// onto ExpressionType.
    #[logfn_inputs(TRACE)]
    fn get_type_for_local(&self, ordinal: usize) -> ExpressionType {
        let loc = &self.mir.local_decls[mir::Local::from(ordinal)];
        (&loc.ty.sty).into()
    }

    /// Returns None if the type of the return local is () (i.e. void)
    fn get_return_type(&self) -> Option<ExpressionType> {
        let return_loc = &self.mir.local_decls[mir::Local::from(0u32)];
        if let TyKind::Tuple(fields) = return_loc.ty.sty {
            if fields.is_empty() {
                return None;
            }
        }
        Some((&return_loc.ty.sty).into())
    }

    /// Do a topological sort, breaking loops by preferring lower block indices, using dominance
    /// to determine if there is a loop (if a is predecessor of b and b dominates a then they
    /// form a loop and we'll emit the one with the lower index first).
    #[logfn_inputs(TRACE)]
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
        for pred_bb in self.mir.predecessors_for(root_block).iter() {
            if already_added.contains(pred_bb) {
                continue;
            };
            if dominators.is_dominated_by(*pred_bb, root_block) {
                continue;
            }
            self.add_predecessors_then_root_block(
                *pred_bb,
                dominators,
                block_indices,
                already_added,
            );
        }
        assume!(block_indices.len() < std::usize::MAX); // We'll run out of memory long  before this overflows
        block_indices.push(root_block);
    }

    // Perform a topological sort on the basic blocks so that blocks are analyzed after their
    // predecessors (except in the case of loop anchors).
    #[logfn_inputs(TRACE)]
    fn get_sorted_block_indices(&mut self) -> Vec<mir::BasicBlock> {
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
        block_indices
    }

    /// Analyze the body and store a summary of its behavior in self.summary_cache.
    /// Returns true if the newly computed summary is different from the summary (if any)
    /// that is already in the cache.
    #[logfn_inputs(TRACE)]
    pub fn visit_body(&mut self, function_name: &str) -> (Option<Summary>, u64) {
        let mut block_indices = self.get_sorted_block_indices();

        let (mut in_state, mut out_state) =
            <MirVisitor<'a, 'b, 'tcx, E>>::initialize_state_maps(&block_indices);

        // The entry block has no predecessors and its initial state is the function parameters
        // (which we omit here so that we can lazily provision them with additional context)
        // as well any promoted constants.
        let first_state = self.promote_constants(function_name);

        let elapsed_time_in_seconds = self.compute_fixed_point(
            function_name,
            &mut block_indices,
            &mut in_state,
            &mut out_state,
            &first_state,
        );

        if elapsed_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
            return (None, elapsed_time_in_seconds);
        }

        // Now traverse the blocks again, doing checks and emitting diagnostics.
        // in_state[bb] is now complete for every basic block bb in the body.
        self.check_for_errors(&block_indices, &in_state);

        // Now create a summary of the body that can be in-lined into call sites.
        let mut summary = summaries::summarize(
            self.mir.arg_count,
            self.get_return_type(),
            &self.exit_environment,
            &self.preconditions,
            &self.post_condition,
            self.unwind_condition.clone(),
            &self.unwind_environment,
            *self.tcx,
        );
        let changed = {
            let old_summary = self.summary_cache.get_summary_for(self.def_id, None);
            if self.outer_fixed_point_iteration > 2 {
                summary = old_summary.widen_with(&summary);
            }
            !summary.is_subset_of(old_summary)
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

    /// Compute a fixed point, which is a value of out_state that will not grow with more iterations.
    #[logfn_inputs(TRACE)]
    fn compute_fixed_point(
        &mut self,
        function_name: &str,
        mut block_indices: &mut Vec<mir::BasicBlock>,
        mut in_state: &mut HashMap<mir::BasicBlock, Environment>,
        mut out_state: &mut HashMap<mir::BasicBlock, Environment>,
        first_state: &Environment,
    ) -> u64 {
        let mut elapsed_time_in_seconds = 0;
        let mut iteration_count = 0;
        let mut changed = true;
        while changed {
            self.fresh_variable_offset = 0;
            changed = self.visit_blocks(
                &mut block_indices,
                &mut in_state,
                &mut out_state,
                &first_state,
                iteration_count,
            );
            elapsed_time_in_seconds = self.start_instant.elapsed().as_secs();
            if elapsed_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
                break;
            }
            if iteration_count > k_limits::MAX_FIXPOINT_ITERATIONS {
                warn!("fixed point loop diverged in body of {}", function_name);
                break;
            }
            iteration_count += 1;
        }
        if iteration_count > 10 {
            warn!(
                "Fixed point loop took {} iterations for {}.",
                iteration_count, function_name
            );
        }
        trace!(
            "Fixed point loop took {} iterations for {}, now checking for errors.",
            iteration_count,
            function_name
        );
        elapsed_time_in_seconds
    }

    #[logfn_inputs(TRACE)]
    fn check_for_errors(
        &mut self,
        block_indices: &[mir::BasicBlock],
        in_state: &HashMap<mir::BasicBlock, Environment>,
    ) {
        self.check_for_errors = true;
        for bb in block_indices.iter() {
            let i_state = (&in_state[bb]).clone();
            self.current_environment = i_state;
            self.visit_basic_block(*bb);
        }
    }

    #[logfn_inputs(TRACE)]
    fn initialize_state_maps(
        block_indices: &[mir::BasicBlock],
    ) -> (
        HashMap<mir::BasicBlock, Environment>,
        HashMap<mir::BasicBlock, Environment>,
    ) {
        // in_state[bb] is the join (or widening) of the out_state values of each predecessor of bb
        let mut in_state: HashMap<mir::BasicBlock, Environment> = HashMap::new();
        // out_state[bb] is the environment that results from analyzing block bb, given in_state[bb]
        let mut out_state: HashMap<mir::BasicBlock, Environment> = HashMap::new();
        for bb in block_indices.iter() {
            in_state.insert(*bb, Environment::default());
            out_state.insert(*bb, Environment::default());
        }
        (in_state, out_state)
    }

    /// Visits each block in block_indices, after computing a precondition and initial state for
    /// each block by joining together the exit conditions and exit states of its predecessors.
    /// Returns true if one or more of the blocks changed their output states.
    #[logfn_inputs(TRACE)]
    fn visit_blocks(
        &mut self,
        block_indices: &mut Vec<mir::BasicBlock>,
        in_state: &mut HashMap<mir::BasicBlock, Environment>,
        out_state: &mut HashMap<mir::BasicBlock, Environment>,
        first_state: &Environment,
        iteration_count: usize,
    ) -> bool {
        let mut changed = false;
        for bb in block_indices.iter() {
            let elapsed_time_in_seconds = self.start_instant.elapsed().as_secs();
            if elapsed_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
                break;
            }

            // Merge output states of predecessors of bb
            let i_state = if bb.index() == 0 {
                first_state.clone()
            } else {
                self.get_initial_state_from_predecessors(*bb, in_state, out_state, iteration_count)
            };
            // Analyze the basic block
            in_state.insert(*bb, i_state.clone());
            self.current_environment = i_state;
            self.visit_basic_block(*bb);

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
                out_state
                    .get_mut(bb)
                    .expect("incorrectly initialized out_state")
                    .exit_conditions = self.current_environment.exit_conditions.clone();
            }
        }
        changed
    }

    /// Join the exit states from all predecessors blocks to get the entry state fo this block.
    /// If a predecessor has not yet been analyzed, its state does not form part of the join.
    /// If no predecessors have been analyzed, the entry state is a default entry state with an
    /// entry condition of TOP.
    #[logfn_inputs(TRACE)]
    fn get_initial_state_from_predecessors(
        &mut self,
        bb: mir::BasicBlock,
        in_state: &HashMap<mir::BasicBlock, Environment>,
        out_state: &HashMap<mir::BasicBlock, Environment>,
        iteration_count: usize,
    ) -> Environment {
        let mut predecessor_states_and_conditions: Vec<(&Environment, Option<&Rc<AbstractValue>>)> =
            self.mir
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
            // nothing is currently known about the predecessors
            let mut i_state = in_state[&bb].clone();
            i_state.entry_condition = Rc::new(abstract_value::TOP);
            i_state
        } else {
            // We want to do right associative operations and that is easier if we reverse.
            predecessor_states_and_conditions.reverse();
            let (p_state, pred_exit_condition) = predecessor_states_and_conditions[0];
            let mut i_state = p_state.clone();
            i_state.entry_condition = pred_exit_condition
                .expect("something went wrong with filter")
                .clone();
            for (p_state, pred_exit_condition) in predecessor_states_and_conditions.iter().skip(1) {
                let mut path_condition = pred_exit_condition
                    .expect("something went wrong with filter")
                    .clone();
                if path_condition.as_bool_if_known().unwrap_or(false) {
                    // A true path condition tells us nothing. If we are already widening,
                    // then replace the true condition with equalities from the corresponding
                    // environment.
                    path_condition =
                        path_condition.add_equalities_for_widened_vars(p_state, &i_state);
                }
                // Once all paths have already been analyzed for a second time (iteration_count == 2)
                // all blocks not involved in loops will have their final values.
                // If there are no loops, the next iteration will be a no-op, but since we
                // don't know if there are loops or not, we do iteration_count == 3 while still
                // joining. Once we get to iteration_count == 4, we start widening in
                // order to converge on a fixed point.
                let mut j_state = if iteration_count < 4 {
                    p_state.join(&i_state, &path_condition)
                } else {
                    p_state.widen(&i_state, &path_condition)
                };
                let joined_condition = path_condition.or(i_state.entry_condition.clone());
                if joined_condition.expression_size > k_limits::MAX_EXPRESSION_SIZE {
                    j_state.entry_condition = Rc::new(abstract_value::TRUE);
                } else {
                    j_state.entry_condition = joined_condition;
                }
                i_state = j_state;
            }
            i_state
        }
    }

    /// Use the visitor to compute the state corresponding to promoted constants.
    #[logfn_inputs(TRACE)]
    fn promote_constants(&mut self, function_name: &str) -> Environment {
        let mut state_with_parameters = Environment::default();
        let saved_mir = self.mir;
        let result_root: Rc<Path> = Rc::new(PathEnum::LocalVariable { ordinal: 0 }.into());
        for (ordinal, constant_mir) in self.mir.promoted.iter().enumerate() {
            self.mir = constant_mir;
            let result_type = self.get_type_for_local(0);
            self.visit_promoted_constants_block(function_name);

            let mut promoted_root: Rc<Path> =
                Rc::new(PathEnum::PromotedConstant { ordinal }.into());
            let value = self.lookup_path_and_refine_result(result_root.clone(), result_type);
            state_with_parameters.update_value_at(promoted_root.clone(), value.clone());
            if let Expression::AbstractHeapAddress(ordinal) = &value.expression {
                promoted_root = Rc::new(PathEnum::AbstractHeapAddress { ordinal: *ordinal }.into());
            }
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

    /// Computes a fixed point over the blocks of the MIR for a promoted constant block
    #[logfn_inputs(TRACE)]
    fn visit_promoted_constants_block(&mut self, function_name: &str) {
        let mut block_indices = self.get_sorted_block_indices();

        let (mut in_state, mut out_state) =
            <MirVisitor<'a, 'b, 'tcx, E>>::initialize_state_maps(&block_indices);

        // The entry block has no predecessors and its initial state is the function parameters
        // (which we omit here so that we can lazily provision them with additional context).
        let first_state = Environment::default();

        self.compute_fixed_point(
            function_name,
            &mut block_indices,
            &mut in_state,
            &mut out_state,
            &first_state,
        );

        self.check_for_errors(&block_indices, &in_state);
    }

    /// Visits each statement in order and then visits the terminator.
    #[logfn_inputs(TRACE)]
    fn visit_basic_block(&mut self, bb: mir::BasicBlock) {
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
    #[logfn_inputs(TRACE)]
    fn visit_statement(&mut self, location: mir::Location, statement: &mir::Statement<'tcx>) {
        self.current_location = location;
        let mir::Statement { kind, source_info } = statement;
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
            mir::StatementKind::Nop => (),
        }
    }

    /// Write the RHS Rvalue to the LHS Place.
    #[logfn_inputs(TRACE)]
    fn visit_assign(&mut self, place: &mir::Place<'tcx>, rvalue: &mir::Rvalue<'tcx>) {
        let path = self.visit_place(place);
        self.visit_rvalue(path, rvalue);
    }

    /// Write the discriminant for a variant to the enum Place.
    #[logfn_inputs(TRACE)]
    fn visit_set_discriminant(
        &mut self,
        place: &mir::Place<'tcx>,
        variant_index: rustc::ty::layout::VariantIdx,
    ) {
        let target_path = Path::new_discriminant(self.visit_place(place));
        let index_val = Rc::new(
            self.constant_value_cache
                .get_u128_for(variant_index.as_usize() as u128)
                .clone()
                .into(),
        );
        self.current_environment
            .update_value_at(target_path, index_val);
    }

    /// Start a live range for the storage of the local.
    #[logfn_inputs(TRACE)]
    fn visit_storage_live(&mut self, local: mir::Local) {}

    /// End the current live range for the storage of the local.
    #[logfn_inputs(TRACE)]
    fn visit_storage_dead(&mut self, local: mir::Local) {
        let path = Rc::new(
            PathEnum::LocalVariable {
                ordinal: local.as_usize(),
            }
            .into(),
        );
        self.current_environment
            .update_value_at(path, abstract_value::BOTTOM.into());
    }

    /// Execute a piece of inline Assembly.
    #[logfn_inputs(TRACE)]
    fn visit_inline_asm(&mut self, inline_asm: &mir::InlineAsm<'tcx>) {
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
    fn visit_terminator(&mut self, source_info: mir::SourceInfo, kind: &mir::TerminatorKind<'tcx>) {
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
    #[logfn_inputs(TRACE)]
    fn visit_goto(&mut self, target: mir::BasicBlock) {
        // Propagate the entry condition to the successor block.
        self.current_environment.exit_conditions = self
            .current_environment
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
    #[logfn_inputs(TRACE)]
    fn visit_switch_int(
        &mut self,
        discr: &mir::Operand<'tcx>,
        switch_ty: rustc::ty::Ty<'tcx>,
        values: &[u128],
        targets: &[mir::BasicBlock],
    ) {
        assume!(targets.len() == values.len() + 1);
        let mut default_exit_condition = self.current_environment.entry_condition.clone();
        let discr = self.visit_operand(discr);
        let discr = discr.as_int_if_known().unwrap_or(discr);
        for i in 0..values.len() {
            let val: Rc<AbstractValue> = Rc::new(ConstantDomain::U128(values[i]).into());
            let cond = discr.equals(val);
            let exit_condition = self.current_environment.entry_condition.and(cond.clone());
            let not_cond = cond.logical_not();
            default_exit_condition = default_exit_condition.and(not_cond);
            let target = targets[i];
            self.current_environment.exit_conditions = self
                .current_environment
                .exit_conditions
                .insert(target, exit_condition);
        }
        self.current_environment.exit_conditions = self
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

    /// Indicates a normal return. The return place should have been filled in by now.
    #[logfn_inputs(TRACE)]
    fn visit_return(&mut self) {
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
    #[logfn_inputs(TRACE)]
    fn visit_unreachable(&mut self) {
        // An unreachable terminator is the compiler's way to tell us that this block will
        // actually never be reached because the type system says so.
        // Why it is necessary in such a case to actually generate unreachable code is something
        // to ponder, but it is not our concern.
        // We don't have to do anything more here because this block precedes no other block.
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
        self.current_environment.exit_conditions = self
            .current_environment
            .exit_conditions
            .insert(target, self.current_environment.entry_condition.clone());
        if let Some(unwind_target) = unwind {
            self.current_environment.exit_conditions =
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
        self.fresh_variable_offset += 1_000_000;
        let func_to_call = self.visit_operand(func);
        let known_name = if let Expression::CompileTimeConstant(fun) = &func_to_call.expression {
            if let ConstantDomain::Function { known_name, .. } = fun {
                known_name
            } else {
                &KnownFunctionNames::None
            }
        } else {
            &KnownFunctionNames::None
        };
        let actual_args: Vec<(Rc<Path>, Rc<AbstractValue>)> = args
            .iter()
            .map(|arg| (self.get_operand_path(arg), self.visit_operand(arg)))
            .collect();
        if self.handled_as_special_function_call(known_name, &actual_args, destination, cleanup) {
            return;
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
    }

    /// If the current call is to a well known function for which we don't have a cached summary,
    /// this function will update the environment as appropriate and return true. If the return
    /// result is false, just carry on with the normal logic.
    #[logfn_inputs(TRACE)]
    fn handled_as_special_function_call(
        &mut self,
        known_name: &KnownFunctionNames,
        actual_args: &[(Rc<Path>, Rc<AbstractValue>)],
        destination: &Option<(mir::Place<'tcx>, mir::BasicBlock)>,
        cleanup: Option<mir::BasicBlock>,
    ) -> bool {
        match *known_name {
            KnownFunctionNames::MiraiAssume => {
                checked_assume!(actual_args.len() == 1);
                if self.check_for_errors {
                    self.report_calls_to_special_functions(known_name, actual_args);
                }
                self.handle_assume(&actual_args, destination, cleanup);
                return true;
            }
            KnownFunctionNames::MiraiGetModelField => {
                if let Some((place, target)) = destination {
                    let rtype = self.get_place_type(place);
                    checked_assume!(actual_args.len() == 3);

                    // The current value, if any, of the model field are a set of (path, value) pairs
                    // where each path is rooted by qualifier.model_field(..)
                    let qualifier = actual_args[0].0.clone();
                    let field_name = self.coerce_to_string(&actual_args[1].1);
                    let rpath = Path::new_model_field(qualifier, field_name)
                        .refine_paths(&self.current_environment);

                    let target_path = self.visit_place(place);
                    if self.current_environment.value_at(&rpath).is_some() {
                        // Move the model field (path, val) pairs to the target (i.e. the place where
                        // the return value of call to the mirai_get_model_field function would go if
                        // it were a normal call.
                        self.copy_or_move_elements(target_path, rpath, rtype, true);
                    } else {
                        // If there is no value for the model field in the environment, we should
                        // use the default value, but only the qualifier is not rooted in a parameter
                        // value since only the caller will know what the values of the fields are.
                        match &actual_args[0].1.expression {
                            Expression::Variable { .. } | Expression::Reference(..) => {
                                let rval = AbstractValue::make_from(
                                    Expression::UnknownModelField {
                                        path: rpath,
                                        default: actual_args[2].1.clone(),
                                    },
                                    1,
                                );
                                self.current_environment.update_value_at(target_path, rval);
                            }
                            _ => {
                                let rpath = actual_args[2].0.clone();
                                self.copy_or_move_elements(target_path, rpath, rtype, true);
                            }
                        }
                    }
                    let exit_condition = self.current_environment.entry_condition.clone();
                    self.current_environment.exit_conditions = self
                        .current_environment
                        .exit_conditions
                        .insert(*target, exit_condition);
                } else {
                    unreachable!();
                }
                return true;
            }
            KnownFunctionNames::MiraiPostcondition => {
                checked_assume!(actual_args.len() == 3);
                if self.check_for_errors {
                    self.report_calls_to_special_functions(known_name, actual_args);
                }
                self.handle_post_condition(&actual_args, destination);
                return true;
            }
            KnownFunctionNames::MiraiPreconditionStart => {
                self.handle_precondition_start(destination);
                return true;
            }
            KnownFunctionNames::MiraiPrecondition => {
                checked_assume!(actual_args.len() == 2);
                self.handle_precondition(&actual_args);
                self.handle_assume(&actual_args, destination, cleanup);
                return true;
            }
            KnownFunctionNames::MiraiSetModelField => {
                if let Some((_, target)) = destination {
                    self.handle_set_model_field(&actual_args, *target);
                } else {
                    unreachable!();
                }
                return true;
            }
            KnownFunctionNames::MiraiShallowClone => {
                if let Some((place, target)) = destination {
                    checked_assume!(actual_args.len() == 1);
                    let rpath = actual_args[0].0.clone();
                    let rtype = self.get_place_type(place);
                    let target_path = self.visit_place(place);
                    self.copy_or_move_elements(target_path, rpath, rtype, false);
                    let exit_condition = self.current_environment.entry_condition.clone();
                    self.current_environment.exit_conditions = self
                        .current_environment
                        .exit_conditions
                        .insert(*target, exit_condition);
                } else {
                    unreachable!();
                }
                return true;
            }
            KnownFunctionNames::MiraiResult => {
                if let Some((place, target)) = destination {
                    let target_path = self.visit_place(place);
                    let target_type = self.get_place_type(place);
                    let return_value_path = Rc::new(PathEnum::LocalVariable { ordinal: 0 }.into());
                    let return_value =
                        self.lookup_path_and_refine_result(return_value_path, target_type);
                    self.current_environment
                        .update_value_at(target_path, return_value);
                    let exit_condition = self.current_environment.entry_condition.clone();
                    self.current_environment.exit_conditions = self
                        .current_environment
                        .exit_conditions
                        .insert(*target, exit_condition);
                } else {
                    unreachable!();
                }
                return true;
            }
            KnownFunctionNames::MiraiVerify => {
                checked_assume!(actual_args.len() == 2);
                if self.check_for_errors {
                    self.report_calls_to_special_functions(known_name, actual_args);
                }
                self.handle_assume(&actual_args[0..1], destination, cleanup);
                return true;
            }
            KnownFunctionNames::StdBeginPanic => {
                if self.check_for_errors {
                    self.report_calls_to_special_functions(known_name, actual_args);
                }
                if let Some((_, target)) = destination {
                    self.current_environment.exit_conditions = self
                        .current_environment
                        .exit_conditions
                        .insert(*target, abstract_value::FALSE.into());
                }
                return true;
            }
            _ => {
                let result = self.try_to_inline_standard_ops_func(known_name, &actual_args);
                if !result.is_bottom() {
                    if let Some((place, target)) = destination {
                        let target_path = self.visit_place(place);
                        self.current_environment
                            .update_value_at(target_path, result);
                        let exit_condition = self.current_environment.entry_condition.clone();
                        self.current_environment.exit_conditions = self
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

    fn handle_set_model_field(
        &mut self,
        actual_args: &&[(Rc<Path>, Rc<AbstractValue>)],
        target: mir::BasicBlock,
    ) {
        checked_assume!(actual_args.len() == 3);
        let qualifier = actual_args[0].0.clone();
        let field_name = self.coerce_to_string(&actual_args[1].1);
        let target_path =
            Path::new_model_field(qualifier, field_name).refine_paths(&self.current_environment);
        let rpath = actual_args[2].0.clone();
        self.copy_or_move_elements(target_path, rpath, ExpressionType::NonPrimitive, true);
        let exit_condition = self.current_environment.entry_condition.clone();
        self.current_environment.exit_conditions = self
            .current_environment
            .exit_conditions
            .insert(target, exit_condition);
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
                let error = self.session.struct_span_err(
                    self.current_span,
                    "this argument should be a string literal, do not call this function directly",
                );
                self.emit_diagnostic(error);
                Rc::new("dummy argument".to_string())
            }
        }
    }

    /// Adds the first and only value in actual_args to the path condition of the destination.
    /// No check is performed, since we get to assume this condition without proof.
    #[logfn_inputs(TRACE)]
    fn handle_assume(
        &mut self,
        actual_args: &[(Rc<Path>, Rc<AbstractValue>)],
        destination: &Option<(mir::Place<'tcx>, mir::BasicBlock)>,
        cleanup: Option<mir::BasicBlock>,
    ) {
        precondition!(actual_args.len() == 1);
        let assumed_condition = &actual_args[0].1;
        let exit_condition = self
            .current_environment
            .entry_condition
            .and(assumed_condition.clone());
        if let Some((_, target)) = destination {
            self.current_environment.exit_conditions = self
                .current_environment
                .exit_conditions
                .insert(*target, exit_condition);
        } else {
            unreachable!();
        }
        if let Some(cleanup_target) = cleanup {
            self.current_environment.exit_conditions = self
                .current_environment
                .exit_conditions
                .insert(cleanup_target, abstract_value::FALSE.into());
        }
    }

    fn handle_post_condition(
        &mut self,
        actual_args: &[(Rc<Path>, Rc<AbstractValue>)],
        destination: &Option<(mir::Place<'tcx>, mir::BasicBlock)>,
    ) {
        precondition!(actual_args.len() == 3);
        let condition = actual_args[0].1.clone();
        let exit_condition = self.current_environment.entry_condition.and(condition);
        if let Some((_, target)) = destination {
            self.current_environment.exit_conditions = self
                .current_environment
                .exit_conditions
                .insert(*target, exit_condition);
        } else {
            unreachable!();
        }
    }

    /// It is bad style for a precondition to be reached conditionally, since well, that condition
    /// should be part of the precondition.
    #[logfn_inputs(TRACE)]
    fn handle_precondition_start(
        &mut self,
        destination: &Option<(mir::Place<'tcx>, mir::BasicBlock)>,
    ) {
        if self.check_for_errors
            && self.check_for_unconditional_precondition
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
            self.check_for_unconditional_precondition = false;
        }
        let exit_condition = self.current_environment.entry_condition.clone();
        if let Some((_, target)) = destination {
            self.current_environment.exit_conditions = self
                .current_environment
                .exit_conditions
                .insert(*target, exit_condition);
        } else {
            unreachable!();
        }
    }

    /// Adds the first and only value in actual_args to the current list of preconditions.
    /// No check is performed, since we get to assume the caller has verified this condition.
    #[logfn_inputs(TRACE)]
    fn handle_precondition(&mut self, actual_args: &[(Rc<Path>, Rc<AbstractValue>)]) {
        precondition!(actual_args.len() == 2);
        if self.check_for_errors {
            let condition = actual_args[0].1.clone();
            let message = self.coerce_to_string(&actual_args[1].1);
            let precondition = Precondition {
                condition,
                message,
                provenance: None,
                spans: vec![self.current_span],
            };
            self.preconditions.push(precondition);
        }
    }

    /// Standard functions that represent an alternative way to perform operations for which
    /// there are MIR operations should be normalized into the corresponding MIR operations.
    /// In some cases this can be done via a summary, but if not this is the place to do it.
    /// Right now, that means core::slice::len becomes a path with the ArrayLength selector
    /// since there is no way to write a summary to that effect in Rust itself.
    #[logfn_inputs(TRACE)]
    fn try_to_inline_standard_ops_func(
        &mut self,
        known_name: &KnownFunctionNames,
        args: &[(Rc<Path>, Rc<AbstractValue>)],
    ) -> Rc<AbstractValue> {
        if *known_name == KnownFunctionNames::CoreSliceLen {
            checked_assume!(args.len() == 1);
            let slice_val = &args[0].1;
            let qualifier = match &slice_val.expression {
                Expression::Reference(path) => Some(path.clone()),
                Expression::Variable { path, .. } => Some(path.clone()),
                Expression::AbstractHeapAddress(ordinal) => Some(Rc::new(
                    PathEnum::AbstractHeapAddress { ordinal: *ordinal }.into(),
                )),
                _ => None,
            };
            if let Some(qualifier) = qualifier {
                let len_path = Path::new_length(qualifier);
                return self.lookup_path_and_refine_result(len_path, ExpressionType::Usize);
            }
        }
        if *known_name == KnownFunctionNames::CoreStrLen {
            checked_assume!(args.len() == 1);
            let str_val = &args[0].1;
            let qualifier = match &str_val.expression {
                Expression::Reference(path) => {
                    let len_path = Path::new_string_length(path.clone());
                    let res = self.lookup_path_and_refine_result(len_path, ExpressionType::U128);
                    Some(res)
                }
                Expression::CompileTimeConstant(ConstantDomain::Str(s)) => {
                    Some(Rc::new(ConstantDomain::U128(s.len() as u128).into()))
                }
                _ => None,
            };
            if let Some(qualifier) = qualifier {
                return qualifier;
            }
        }
        abstract_value::BOTTOM.into()
    }

    /// Returns a summary of the function to call, obtained from the summary cache.
    #[logfn_inputs(TRACE)]
    fn get_function_summary(&mut self, func_to_call: &Rc<AbstractValue>) -> Summary {
        if let Expression::CompileTimeConstant(ConstantDomain::Function {
            def_id: Some(def_id),
            function_id: Some(function_id),
            summary_cache_key,
            argument_type_key,
            ..
        }) = &func_to_call.expression
        {
            self.summary_cache
                .get_summary_for_function_constant(
                    *def_id,
                    *function_id,
                    summary_cache_key,
                    argument_type_key,
                    self.def_id,
                )
                .clone()
        } else {
            Summary::default()
        }
    }

    /// Checks if the preconditions obtained from the summary of the function being called
    /// are met by the current state and arguments of the calling function.
    /// Preconditions that are definitely false generate diagnostic messages.
    /// Preconditions that are maybe false become preconditions of the calling function.
    #[logfn_inputs(TRACE)]
    fn check_function_preconditions(
        &mut self,
        actual_args: &[(Rc<Path>, Rc<AbstractValue>)],
        function_summary: &Summary,
        func_to_call: &Rc<AbstractValue>,
    ) {
        verify!(self.check_for_errors);
        for precondition in &function_summary.preconditions {
            let mut refined_condition = precondition
                .condition
                .refine_parameters(actual_args, self.fresh_variable_offset)
                .refine_paths(&self.current_environment);
            if self
                .current_environment
                .entry_condition
                .as_bool_if_known()
                .is_none()
            {
                refined_condition =
                    refined_condition.refine_with(&self.current_environment.entry_condition, 0);
            }
            let (refined_precondition_as_bool, entry_cond_as_bool) =
                self.check_condition_value_and_reachability(&refined_condition);

            if refined_precondition_as_bool.unwrap_or(false) {
                // The precondition is definitely true.
                continue;
            };
            if !refined_precondition_as_bool.unwrap_or(true) {
                // The precondition is definitely false.
                if entry_cond_as_bool.unwrap_or(false) && is_public(self.def_id, &self.tcx) {
                    // If this function is called, we always get to this call.
                    // Since this function is public, we have assume that it will get called.
                    // If this function is not meant to be called, it should add an explicit
                    // false precondition of its own.
                    if !self
                        .already_report_errors_for_call_to
                        .contains(func_to_call)
                    {
                        self.emit_diagnostic_for_precondition(precondition, false);
                        self.already_report_errors_for_call_to
                            .insert(func_to_call.clone());
                    }
                } else {
                    // If the entry condition is not known to be true, it will serve as the
                    // promoted precondition and the program is only faulty if a caller enables
                    // the current function to reach this call.
                    // If the entry condition is known to be true, the program can still
                    // be regarded as correct if this function is never called. Since the function
                    // is not public in that case, we can check that no call is ever reached.
                }
            } else {
                // The precondition may or may not be false.
                self.warn_if_public(func_to_call, precondition)
            }

            // Promote the precondition, subject to a k-limit.
            if self.preconditions.len() < k_limits::MAX_INFERRED_PRECONDITIONS {
                // Promote the callee precondition to a precondition of the current function.
                // Unless, of course, if the precondition is already a precondition of the
                // current function.
                if self
                    .preconditions
                    .iter()
                    .any(|pc| pc.spans.last() == precondition.spans.last())
                {
                    continue;
                }
                let promoted_condition = self
                    .current_environment
                    .entry_condition
                    .logical_not()
                    .or(refined_condition);
                let mut stacked_spans = vec![self.current_span];
                stacked_spans.append(&mut precondition.spans.clone());
                let promoted_precondition = Precondition {
                    condition: promoted_condition,
                    message: precondition.message.clone(),
                    provenance: precondition.provenance.clone(),
                    spans: stacked_spans,
                };
                self.preconditions.push(promoted_precondition);
            }
        }
    }

    /// If the current function is public, or if there are already too many promoted preconditions,
    /// emit a warning that the given precondition of the function being called is not known to
    /// be true at this point and/or the call is not known to be unreachable.
    #[logfn_inputs(TRACE)]
    fn warn_if_public(&mut self, func_to_call: &Rc<AbstractValue>, precondition: &Precondition) {
        if is_public(self.def_id, &self.tcx)
            || self.preconditions.len() >= k_limits::MAX_INFERRED_PRECONDITIONS
        {
            if !self
                .already_report_errors_for_call_to
                .contains(func_to_call)
            {
                self.emit_diagnostic_for_precondition(precondition, true);
                self.already_report_errors_for_call_to
                    .insert(func_to_call.clone());
            }
        } else {
            // Since the function is not public, we assume that we get to see
            // every call to this function, so just rely on the inferred precondition.
        }
    }

    /// Emit a diagnostic to the effect that the current call might violate a the given precondition
    /// of the called function. Use the provenance and spans of the precondition to point out related locations.
    #[logfn_inputs(TRACE)]
    fn emit_diagnostic_for_precondition(&mut self, precondition: &Precondition, warn: bool) {
        let mut diagnostic = if warn {
            Rc::new(format!("possible {}", precondition.message))
        } else {
            precondition.message.clone()
        };
        if let Some(provenance) = &precondition.provenance {
            let mut buffer = diagnostic.to_string();
            buffer.push_str(", defined in ");
            buffer.push_str(provenance.as_str());
            diagnostic = Rc::new(buffer);
        }
        let span = self.current_span;
        let mut err = self.session.struct_span_warn(span, diagnostic.as_str());
        if !precondition.spans.is_empty() {
            err.span_note(precondition.spans.clone(), "related location");
        }
        self.emit_diagnostic(err);
    }

    /// Updates the current state to reflect the effects of a normal return from the function call.
    #[logfn_inputs(TRACE)]
    fn transfer_and_refine_normal_return_state(
        &mut self,
        destination: &Option<(mir::Place<'tcx>, mir::BasicBlock)>,
        actual_args: &[(Rc<Path>, Rc<AbstractValue>)],
        function_summary: &Summary,
    ) {
        if let Some((place, target)) = destination {
            // Assign function result to place
            let target_path = self.visit_place(place);
            let return_value_path = Rc::new(PathEnum::LocalVariable { ordinal: 0 }.into());
            // Transfer side effects

            // Effects on the call result
            self.transfer_and_refine(
                &function_summary.side_effects,
                target_path,
                &return_value_path,
                actual_args,
            );

            // Effects on the call arguments
            for (i, (target_path, _)) in actual_args.iter().enumerate() {
                let parameter_path = Rc::new(PathEnum::LocalVariable { ordinal: i + 1 }.into());
                self.transfer_and_refine(
                    &function_summary.side_effects,
                    target_path.clone(),
                    &parameter_path,
                    actual_args,
                );
            }

            // Effects on the heap
            for (path, value) in function_summary.side_effects.iter() {
                if path.is_rooted_by_abstract_heap_address() {
                    let rvalue = value
                        .clone()
                        .refine_parameters(actual_args, self.fresh_variable_offset)
                        .refine_paths(&self.current_environment);
                    self.current_environment
                        .update_value_at(path.clone(), rvalue);
                }
            }

            // Add post conditions to entry condition
            let mut exit_condition = self.current_environment.entry_condition.clone();
            if let Some(unwind_condition) = &function_summary.unwind_condition {
                exit_condition = exit_condition.and(unwind_condition.logical_not());
            }
            if let Some(post_condition) = &function_summary.post_condition {
                let refined_post_condition = post_condition
                    .refine_parameters(actual_args, self.fresh_variable_offset)
                    .refine_paths(&self.current_environment);
                exit_condition = exit_condition.and(refined_post_condition);
            }

            self.current_environment.exit_conditions = self
                .current_environment
                .exit_conditions
                .insert(*target, exit_condition);
        }
    }

    /// Handle the case where the called function does not complete normally.
    #[logfn_inputs(TRACE)]
    fn transfer_and_refine_cleanup_state(
        &mut self,
        cleanup: Option<mir::BasicBlock>,
        actual_args: &[(Rc<Path>, Rc<AbstractValue>)],
        function_summary: &Summary,
    ) {
        if let Some(cleanup_target) = cleanup {
            for (i, (target_path, _)) in actual_args.iter().enumerate() {
                let parameter_path = Rc::new(PathEnum::LocalVariable { ordinal: i + 1 }.into());
                self.transfer_and_refine(
                    &function_summary.unwind_side_effects,
                    target_path.clone(),
                    &parameter_path,
                    actual_args,
                );
            }
            let mut exit_condition = self.current_environment.entry_condition.clone();
            if let Some(unwind_condition) = &function_summary.unwind_condition {
                exit_condition = exit_condition.and(unwind_condition.clone());
            }
            self.current_environment.exit_conditions = self
                .current_environment
                .exit_conditions
                .insert(cleanup_target, exit_condition);
        }
    }

    /// If the function being called is a special function like mirai_annotations.mirai_verify or
    /// std.panicking.begin_panic then report a diagnostic or create a precondition as appropriate.
    #[logfn_inputs(TRACE)]
    fn report_calls_to_special_functions(
        &mut self,
        known_name: &KnownFunctionNames,
        actual_args: &[(Rc<Path>, Rc<AbstractValue>)],
    ) {
        verify!(self.check_for_errors);
        match known_name {
            KnownFunctionNames::MiraiAssume => {
                assume!(actual_args.len() == 1);
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

                // If the condition is always true, this assumption is redundant
                if cond_as_bool.unwrap_or(false) {
                    let span = self.current_span;
                    let warning = self
                        .session
                        .struct_span_warn(span, "assumption is provably true and can be deleted");
                    self.emit_diagnostic(warning);
                }
            }
            KnownFunctionNames::MiraiPostcondition => {
                if self.post_condition.is_some() {
                    let span = self.current_span;
                    let warning = self
                        .session
                        .struct_span_warn(span, "only one post condition is supported");
                    self.emit_diagnostic(warning);
                }
                assume!(actual_args.len() == 3); // The type checker ensures this.
                let (_, assumption) = &actual_args[1];
                let (_, cond) = &actual_args[0];
                if !assumption.as_bool_if_known().unwrap_or(false) {
                    let message = self.coerce_to_string(&actual_args[2].1);
                    if self.check_condition(cond, message, true).is_none() {
                        self.post_condition = Some(cond.clone());
                    }
                } else {
                    self.post_condition = Some(cond.clone());
                }
            }
            KnownFunctionNames::MiraiVerify => {
                assume!(actual_args.len() == 2); // The type checker ensures this.
                let (_, cond) = &actual_args[0];
                let message = self.coerce_to_string(&actual_args[1].1);
                if let Some(warning) = self.check_condition(cond, message, false) {
                    // Push a precondition so that any known or unknown caller of this function
                    // is warned that this function will fail if the precondition is not met.
                    if self.preconditions.len() < k_limits::MAX_INFERRED_PRECONDITIONS {
                        let condition = self
                            .current_environment
                            .entry_condition
                            .logical_not()
                            .or(cond.clone());
                        let precondition = Precondition {
                            condition,
                            message: Rc::new(warning),
                            provenance: None,
                            spans: vec![self.current_span],
                        };
                        self.preconditions.push(precondition);
                    }
                }
            }
            KnownFunctionNames::StdBeginPanic => {
                let mut path_cond = self.current_environment.entry_condition.as_bool_if_known();
                if path_cond.is_none() {
                    // Try the SMT solver
                    let path_expr = &self.current_environment.entry_condition.expression;
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
                    actual_args[0].1.expression
                {
                    if msg.contains("entered unreachable code") {
                        // We treat unreachable!() as an assumption rather than an assertion to prove.
                        return;
                    } else {
                        msg.clone()
                    }
                } else {
                    Rc::new(String::from("execution panic"))
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
                    let condition = self.current_environment.entry_condition.logical_not();
                    let mut maybe_message = String::from("possible error: ");
                    maybe_message.push_str(msg.as_str());
                    let precondition = Precondition {
                        condition,
                        message: Rc::new(maybe_message),
                        provenance: None,
                        spans: vec![self.current_span],
                    };
                    self.preconditions.push(precondition);
                }
            }
            _ => unreachable!(),
        }
    }

    /// Check if the given condition is reachable and true.
    /// If not issue a warning if the function is public and return the warning message, if
    /// the condition is not a post condition.
    fn check_condition(
        &mut self,
        cond: &Rc<AbstractValue>,
        message: Rc<String>,
        is_post_condition: bool,
    ) -> Option<String> {
        let (cond_as_bool, entry_cond_as_bool) = self.check_condition_value_and_reachability(cond);

        // If we never get here, rather call unreachable!()
        if !entry_cond_as_bool.unwrap_or(true) {
            let span = self.current_span;
            let message = "this is unreachable, mark it as such by using the unreachable! macro";
            let warning = self.session.struct_span_warn(span, message);
            self.emit_diagnostic(warning);
            return None;
        }

        // If the condition is always true when we get here there is nothing to report.
        if cond_as_bool.unwrap_or(false) {
            return None;
        }

        // If the condition is always false, give an error since that is bad style.
        if !cond_as_bool.unwrap_or(true) {
            // If the condition is always false, give a style error
            let span = self.current_span;
            let error = self
                .session
                .struct_span_err(span, "provably false verification condition");
            self.emit_diagnostic(error);
            if !is_post_condition && self.preconditions.len() < k_limits::MAX_INFERRED_PRECONDITIONS
            {
                // promote the path as a precondition. I.e. the program is only correct,
                // albeit badly written, if we never get here.
                let condition = self.current_environment.entry_condition.logical_not();
                let message = Rc::new(format!("possible {}", message));
                let precondition = Precondition {
                    condition,
                    message,
                    provenance: None,
                    spans: vec![span],
                };
                self.preconditions.push(precondition);
            }
            return None;
        }

        let warning = format!("possible {}", message);

        // We might get here, or not, and the condition might be false, or not.
        // Give a warning if we don't know all of the callers, or if we run into a k-limit
        if is_public(self.def_id, &self.tcx)
            || self.preconditions.len() >= k_limits::MAX_INFERRED_PRECONDITIONS
        {
            // We expect public functions to have programmer supplied preconditions
            // that preclude any assertions from failing. So, at this stage we get to
            // complain a bit.
            let span = self.current_span;
            let warning = self.session.struct_span_warn(span, warning.as_str());
            self.emit_diagnostic(warning);
        }

        Some(warning)
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
            let tpath = Rc::new(path.clone())
                .replace_root(source_path, target_path.clone())
                .refine_paths(&self.current_environment);
            let rvalue = value
                .clone()
                .refine_parameters(arguments, self.fresh_variable_offset)
                .refine_paths(&self.current_environment);
            if let Expression::Variable { path, .. } = &rvalue.expression {
                if let PathEnum::LocalVariable { ordinal } = &path.value {
                    if *ordinal >= self.fresh_variable_offset {
                        // A fresh variable from the callee adds no information that is not
                        // already inherent in the target location.
                        self.current_environment.value_map =
                            self.current_environment.value_map.remove(&tpath);
                        continue;
                    }
                }
            }
            for (arg_path, arg_val) in arguments.iter() {
                if arg_val.eq(&rvalue) {
                    let rtype = arg_val.expression.infer_type();
                    self.copy_or_move_elements(tpath.clone(), arg_path.clone(), rtype, false);
                    break;
                }
            }
            let elapsed_time_in_seconds = self.start_instant.elapsed().as_secs();
            if elapsed_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
                return;
            }
            self.current_environment.update_value_at(tpath, rvalue);
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
        let cond_val = self.visit_operand(cond);
        let not_cond_val = cond_val.logical_not();
        // Propagate the entry condition to the successor blocks, conjoined with cond (or !cond).
        if let Some(cleanup_target) = cleanup {
            let cleanup_condition = self.current_environment.entry_condition.and(if expected {
                not_cond_val.clone()
            } else {
                cond_val.clone()
            });
            self.current_environment.exit_conditions = self
                .current_environment
                .exit_conditions
                .insert(cleanup_target, cleanup_condition);
        };
        let exit_condition = self.current_environment.entry_condition.and(if expected {
            cond_val.clone()
        } else {
            not_cond_val.clone()
        });
        self.current_environment.exit_conditions = self
            .current_environment
            .exit_conditions
            .insert(target, exit_condition);
        if self.check_for_errors {
            if let mir::Operand::Constant(..) = cond {
                // Do not complain about compile time constants known to the compiler.
                // Leave that to the compiler.
            } else {
                let (cond_as_bool, entry_cond_as_bool) =
                    self.check_condition_value_and_reachability(&cond_val);

                // Quick exit if things are known.
                if let Some(false) = entry_cond_as_bool {
                    // We can't reach this assertion, so just return.
                    return;
                }
                if cond_as_bool.is_some() {
                    if expected == cond_as_bool.unwrap() {
                        // If the condition is always as expected when we get here, so there is nothing to report.
                        return;
                    }
                    // If we always get here if called, give an error.
                    if entry_cond_as_bool.is_some() && entry_cond_as_bool.unwrap() {
                        let error = msg.description();
                        let span = self.current_span;
                        // For now emit a warning since path conditions are not properly widened
                        // during loops and thus may result in false negatives.
                        let error = self.session.struct_span_warn(span, error);
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
                // After, of course, removing any promoted preconditions that match the current
                // source span.
                let sp = self.current_span;
                self.preconditions.retain(|pc| pc.spans.last() != Some(&sp));
                if self.preconditions.len() < k_limits::MAX_INFERRED_PRECONDITIONS {
                    let expected_cond = if expected {
                        cond_val
                    } else {
                        cond_val.logical_not()
                    };
                    // To make sure that this assertion never fails, we should either never
                    // get here (!entry_condition) or expected_cond should be true.
                    let condition = self
                        .current_environment
                        .entry_condition
                        .logical_not()
                        .or(expected_cond);
                    let message = Rc::new(String::from(msg.description()));
                    let precondition = Precondition {
                        condition,
                        message,
                        provenance: None,
                        spans: vec![self.current_span],
                    };
                    self.preconditions.push(precondition);
                }
            }
        };
    }

    /// Checks the given condition value and also checks if the current entry condition can be true.
    /// If the abstract domains are undecided, resort to using the SMT solver.
    /// Only call this when doing actual error checking, since this is expensive.
    #[logfn_inputs(TRACE)]
    fn check_condition_value_and_reachability(
        &mut self,
        cond_val: &Rc<AbstractValue>,
    ) -> (Option<bool>, Option<bool>) {
        // Check if the condition is always true (or false) if we get here.
        let mut cond_as_bool = cond_val.as_bool_if_known();
        // Check if we can prove that every call to the current function will reach this call site.
        let mut entry_cond_as_bool = self.current_environment.entry_condition.as_bool_if_known();
        // Use SMT solver if need be.
        if entry_cond_as_bool.is_none() {
            // Check if path implies condition
            if self.current_environment.entry_condition.implies(cond_val) {
                return (Some(true), None);
            }
            if self
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
                let ec = &self.current_environment.entry_condition.expression;
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

    #[logfn_inputs(TRACE)]
    fn solve_condition(&mut self, cond_val: &Rc<AbstractValue>) -> Option<bool> {
        let ce = &cond_val.expression;
        let cond_smt_expr = self.smt_solver.get_as_smt_predicate(ce);
        match self.smt_solver.solve_expression(&cond_smt_expr) {
            SmtResult::Unsatisfiable => {
                // If we get here, the solver can prove that cond_val is always false.
                Some(false)
            }
            SmtResult::Satisfiable => {
                // We could get here with cond_val being true. Or perhaps not.
                // So lets see if !cond_val is provably false.
                let not_cond_expr = &cond_val.logical_not().expression;
                let smt_expr = self.smt_solver.get_as_smt_predicate(not_cond_expr);
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
    #[logfn_inputs(TRACE)]
    fn visit_rvalue(&mut self, path: Rc<Path>, rvalue: &mir::Rvalue<'tcx>) {
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
                    ty,
                    user_ty,
                    literal,
                    ..
                } = constant.borrow();
                let const_value = self.visit_constant(ty, *user_ty, &literal.val);
                match &const_value.expression {
                    Expression::AbstractHeapAddress(ordinal) => {
                        let rtype = ExpressionType::Reference;
                        let rpath =
                            Rc::new(PathEnum::AbstractHeapAddress { ordinal: *ordinal }.into());
                        self.copy_or_move_elements(path, rpath, rtype, false);
                    }
                    Expression::CompileTimeConstant(ConstantDomain::Str(val)) => {
                        let rtype = ExpressionType::U128;
                        let rpath: Rc<Path> = Rc::new(
                            PathEnum::Constant {
                                value: Rc::new(ConstantDomain::Str(val.clone()).into()),
                            }
                            .into(),
                        );
                        self.copy_or_move_elements(path.clone(), rpath, rtype, false);
                        self.current_environment.update_value_at(path, const_value);
                    }
                    _ => {
                        self.current_environment.update_value_at(path, const_value);
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
        let rtype = self.get_place_type(place);
        self.copy_or_move_elements(target_path, rpath, rtype, false);
    }

    /// Copies/moves all paths rooted in rpath to corresponding paths rooted in target_path.
    #[logfn_inputs(TRACE)]
    fn copy_or_move_elements(
        &mut self,
        target_path: Rc<Path>,
        rpath: Rc<Path>,
        rtype: ExpressionType,
        move_elements: bool,
    ) {
        let elapsed_time_in_seconds = self.start_instant.elapsed().as_secs();
        if elapsed_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
            return;
        }
        let mut value_map = self.current_environment.value_map.clone();
        // Some qualified rpaths are patterns that represent collections of values.
        // We need to expand the patterns before doing the actual moves.
        if let PathEnum::QualifiedPath {
            ref qualifier,
            ref selector,
            ..
        } = &rpath.value
        {
            match **selector {
                PathSelector::ConstantIndex {
                    offset, from_end, ..
                } => {
                    let index = if from_end {
                        let len_value = self.get_len(qualifier.clone());
                        if let AbstractValue {
                            expression: Expression::CompileTimeConstant(ConstantDomain::U128(len)),
                            ..
                        } = len_value.as_ref()
                        {
                            (*len) - u128::from(offset)
                        } else {
                            unreachable!("PathSelector::ConstantIndex implies the length of the value is known")
                        }
                    } else {
                        u128::from(offset)
                    };
                    let index_val =
                        Rc::new(self.constant_value_cache.get_u128_for(index).clone().into());
                    let index_path = Path::new_index(qualifier.clone(), index_val);
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
                        let len_value = self.get_len(qualifier.clone());
                        if let AbstractValue {
                            expression: Expression::CompileTimeConstant(ConstantDomain::U128(len)),
                            ..
                        } = len_value.as_ref()
                        {
                            u32::try_from(*len).unwrap() - to
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
                        let index_val = Rc::new(
                            self.constant_value_cache
                                .get_u128_for(u128::from(i))
                                .clone()
                                .into(),
                        );
                        let index_path = Path::new_index(qualifier.clone(), index_val);
                        let target_index_val = Rc::new(
                            self.constant_value_cache
                                .get_u128_for(u128::try_from(i - from).unwrap())
                                .clone()
                                .into(),
                        );
                        let indexed_target = Path::new_index(target_path.clone(), target_index_val);
                        self.copy_or_move_elements(
                            indexed_target,
                            index_path,
                            rtype.clone(),
                            move_elements,
                        );
                        let elapsed_time_in_seconds = self.start_instant.elapsed().as_secs();
                        if elapsed_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
                            return;
                        }
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
            let elapsed_time_in_seconds = self.start_instant.elapsed().as_secs();
            if elapsed_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
                return;
            }
            let qualified_path = path.replace_root(&rpath, target_path.clone());
            if move_elements {
                trace!("moving {:?} to {:?}", value, qualified_path);
                value_map = value_map.remove(path);
            } else {
                trace!("copying {:?} to {:?}", value, qualified_path);
            };
            value_map = value_map.insert(qualified_path, value.clone());
        }
        // Now move/copy (rpath, value) itself.
        let mut value = self.lookup_path_and_refine_result(rpath.clone(), rtype);
        if move_elements {
            trace!("moving {:?} to {:?}", value, target_path);
            value_map = value_map.remove(&rpath);
        } else {
            trace!("copying {:?} to {:?}", value, target_path);
            // if the value is a non primitive and a path reference, update the reference to be the new target
            if let Expression::Variable { var_type, .. } = &value.expression {
                if *var_type == ExpressionType::NonPrimitive {
                    value = AbstractValue::make_from(
                        Expression::Variable {
                            path: target_path.clone(),
                            var_type: var_type.clone(),
                        },
                        1,
                    );
                }
            }
        }
        value_map = value_map.insert(target_path, value);
        self.current_environment.value_map = value_map;
    }

    /// For each (path', value) pair in the environment where path' is rooted in place,
    /// add a (path'', value) pair to the environment where path'' is a copy of path re-rooted
    /// with place, and also remove the (path', value) pair from the environment.
    #[logfn_inputs(TRACE)]
    fn visit_used_move(&mut self, target_path: Rc<Path>, place: &mir::Place<'tcx>) {
        let rpath = self.visit_place(place);
        let rtype = self.get_place_type(place);
        self.copy_or_move_elements(target_path, rpath, rtype, true);
    }

    /// path = [x; 32]
    #[logfn_inputs(TRACE)]
    fn visit_repeat(&mut self, path: Rc<Path>, operand: &mir::Operand<'tcx>, count: u64) {
        let length_path = Path::new_length(path);
        let length_value = Rc::new(
            self.constant_value_cache
                .get_u128_for(u128::from(count))
                .clone()
                .into(),
        );
        self.current_environment
            .update_value_at(length_path, length_value);
        //todo: also need to write a path that summarizes count paths and give it the value
        //  of operand.
        //We do not yet have a way to summarize paths.
        //Meanwhile just visit the operand to at least look at its validity.
        self.visit_operand(operand);
    }

    /// path = &x or &mut x
    #[logfn_inputs(TRACE)]
    fn visit_ref(
        &mut self,
        path: Rc<Path>,
        region: rustc::ty::Region<'tcx>,
        borrow_kind: mir::BorrowKind,
        place: &mir::Place<'tcx>,
    ) {
        let value_path = self.visit_place(place);
        let value = match &value_path.value {
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } if *selector.as_ref() == PathSelector::Deref => {
                // We are taking a reference to the result of a deref. This is a bit awkward.
                // The deref essentially does a copy of the value denoted by the qualifier.
                // It this value is structured and not heap allocated, the copy must be done
                // with copy_or_move_elements. We use path as the address of the copy and rely
                // on the type of the value to ensure reference like behavior.
                let rval = self
                    .lookup_path_and_refine_result(qualifier.clone(), ExpressionType::Reference);
                self.copy_or_move_elements(
                    path.clone(),
                    qualifier.clone(),
                    rval.expression.infer_type(),
                    false,
                );
                return;
            }
            PathEnum::PromotedConstant { .. } => {
                if let Some(val) = self.current_environment.value_at(&value_path) {
                    if let Expression::AbstractHeapAddress(ordinal) = &val.expression {
                        let heap_path =
                            Rc::new(PathEnum::AbstractHeapAddress { ordinal: *ordinal }.into());
                        AbstractValue::make_from(Expression::Reference(heap_path), 1)
                    } else {
                        AbstractValue::make_from(Expression::Reference(value_path), 1)
                    }
                } else {
                    AbstractValue::make_from(Expression::Reference(value_path), 1)
                }
            }
            _ => AbstractValue::make_from(Expression::Reference(value_path), 1),
        };
        self.current_environment.update_value_at(path, value);
    }

    /// path = length of a [X] or [X;n] value.
    #[logfn_inputs(TRACE)]
    fn visit_len(&mut self, path: Rc<Path>, place: &mir::Place<'tcx>) {
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
    #[logfn_inputs(TRACE)]
    fn get_len(&mut self, path: Rc<Path>) -> Rc<AbstractValue> {
        let length_path = Path::new_length(path);
        self.lookup_path_and_refine_result(length_path, ExpressionType::Usize)
    }

    /// path = operand as ty.
    #[logfn_inputs(TRACE)]
    fn visit_cast(
        &mut self,
        path: Rc<Path>,
        cast_kind: mir::CastKind,
        operand: &mir::Operand<'tcx>,
        ty: rustc::ty::Ty<'tcx>,
    ) {
        let operand = self.visit_operand(operand);
        let result = if cast_kind == mir::CastKind::Misc {
            operand.cast(ExpressionType::from(&ty.sty))
        } else {
            operand
        };
        self.current_environment.update_value_at(path, result);
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
                let target_type = self.get_target_path_type(&path);
                left.shr(right, target_type)
            }
            mir::BinOp::Sub => left.subtract(right),
        };
        self.current_environment.update_value_at(path, result);
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
        let target_type = self.get_first_part_of_target_path_type_tuple(&path);
        let left = self.visit_operand(left_operand);
        let right = self.visit_operand(right_operand);
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
            _ => unreachable!(),
        };
        let path0 = Path::new_field(path.clone(), 0);
        self.current_environment.update_value_at(path0, result);
        let path1 = Path::new_field(path, 1);
        self.current_environment
            .update_value_at(path1, overflow_flag);
    }

    /// Create a value based on the given type and assign it to path.
    #[logfn_inputs(TRACE)]
    fn visit_nullary_op(&mut self, path: Rc<Path>, null_op: mir::NullOp, ty: rustc::ty::Ty<'tcx>) {
        let value = match null_op {
            mir::NullOp::Box => self.get_new_heap_address(),
            mir::NullOp::SizeOf => {
                //todo: figure out how to get the size from ty.
                Rc::new(abstract_value::TOP)
            }
        };
        self.current_environment.update_value_at(path, value);
    }

    /// Allocates a new heap address and caches it, keyed with the current location
    /// so that subsequent visits deterministically use the same address when processing
    /// the instruction at this location. If we don't do this the fixed point loop wont converge.
    /// Note, however, that this is not good enough for the outer fixed point because the counter
    /// is shared between different functions unless it is reset to 0 for each function.
    #[logfn_inputs(TRACE)]
    fn get_new_heap_address(&mut self) -> Rc<AbstractValue> {
        let addresses = &mut self.heap_addresses;
        let constants = &mut self.constant_value_cache;
        addresses
            .entry(self.current_location)
            .or_insert_with(|| AbstractValue::make_from(constants.get_new_heap_address(), 1))
            .clone()
    }

    /// Apply the given unary operator to the operand and assign to path.
    #[logfn_inputs(TRACE)]
    fn visit_unary_op(&mut self, path: Rc<Path>, un_op: mir::UnOp, operand: &mir::Operand<'tcx>) {
        let operand = self.visit_operand(operand);
        let result = match un_op {
            mir::UnOp::Neg => operand.negate(),
            mir::UnOp::Not => {
                let result_type = self.get_target_path_type(&path);
                if result_type.is_integer() {
                    operand.bit_not(result_type)
                } else {
                    operand.logical_not()
                }
            }
        };
        self.current_environment.update_value_at(path, result);
    }

    /// Read the discriminant of an enum and assign to path.
    #[logfn_inputs(TRACE)]
    fn visit_discriminant(&mut self, path: Rc<Path>, place: &mir::Place<'tcx>) {
        let discriminant_path = Path::new_discriminant(self.visit_place(place));
        let discriminant_type = ExpressionType::Isize;
        let discriminant_value =
            self.lookup_path_and_refine_result(discriminant_path, discriminant_type);
        self.current_environment
            .update_value_at(path, discriminant_value);
    }

    /// Currently only survives in the MIR that MIRAI sees, if the aggregate is an array.
    /// See https://github.com/rust-lang/rust/issues/48193.
    #[logfn_inputs(TRACE)]
    fn visit_aggregate(
        &mut self,
        path: Rc<Path>,
        aggregate_kinds: &mir::AggregateKind<'tcx>,
        operands: &[mir::Operand<'tcx>],
    ) {
        checked_assume!(match *aggregate_kinds {
            mir::AggregateKind::Array(..) => true,
            _ => false,
        });
        if path.path_length() >= k_limits::MAX_PATH_LENGTH {
            // If we get to this limit we have a very weird array. Just use Top.
            self.current_environment
                .update_value_at(path, abstract_value::TOP.into());
            return;
        }
        let aggregate_value = self.get_new_heap_address();
        self.current_environment
            .update_value_at(path.clone(), aggregate_value);
        for (i, operand) in operands.iter().enumerate() {
            let index_value = Rc::new(
                self.constant_value_cache
                    .get_u128_for(i as u128)
                    .clone()
                    .into(),
            );
            let index_path = Path::new_index(path.clone(), index_value);
            self.visit_used_operand(index_path, operand);
        }
        let length_path = Path::new_length(path);
        let length_value = Rc::new(
            self.constant_value_cache
                .get_u128_for(operands.len() as u128)
                .clone()
                .into(),
        );
        self.current_environment
            .update_value_at(length_path, length_value);
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
                    ty,
                    user_ty,
                    literal,
                    ..
                } = constant.borrow();
                let const_value = self.visit_constant(ty, *user_ty, &literal.val);
                self.current_environment
                    .update_value_at(target_path, const_value);
            }
        };
    }

    /// Returns the path (location/lh-value) of the given operand.
    #[logfn_inputs(TRACE)]
    fn get_operand_path(&mut self, operand: &mir::Operand<'tcx>) -> Rc<Path> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => self.visit_place(place),
            mir::Operand::Constant(..) => Rc::new(
                PathEnum::Constant {
                    value: self.visit_operand(operand),
                }
                .into(),
            ),
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
                    ty,
                    user_ty,
                    literal,
                    ..
                } = constant.borrow();
                self.visit_constant(ty, *user_ty, &literal.val)
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
        let place_type = self.get_place_type(place);
        self.lookup_path_and_refine_result(path, place_type)
    }

    /// Move: The value (including old borrows of it) will not be used again.
    ///
    /// Safe for values of all types (modulo future developments towards `?Move`).
    /// Correct usage patterns are enforced by the borrow checker for safe code.
    /// `Copy` may be converted to `Move` to enable "last-use" optimizations.
    #[logfn_inputs(TRACE)]
    fn visit_move(&mut self, place: &mir::Place<'tcx>) -> Rc<AbstractValue> {
        let path = self.visit_place(place);
        let place_type = self.get_place_type(place);
        self.lookup_path_and_refine_result(path, place_type)
    }

    /// Synthesizes a constant value.
    #[logfn_inputs(TRACE)]
    fn visit_constant(
        &mut self,
        ty: Ty<'tcx>,
        user_ty: Option<UserTypeAnnotationIndex>,
        literal: &mir::interpret::ConstValue<'tcx>,
    ) -> Rc<AbstractValue> {
        use rustc::mir::interpret::Scalar;

        match literal {
            mir::interpret::ConstValue::Unevaluated(def_id, ..) => {
                let name = utils::summary_key_str(&self.tcx, *def_id);
                let expression_type: ExpressionType = ExpressionType::from(&ty.sty);
                let path = Rc::new(
                    PathEnum::StaticVariable {
                        def_id: Some(*def_id),
                        summary_cache_key: name,
                        expression_type: expression_type.clone(),
                    }
                    .into(),
                );
                self.lookup_path_and_refine_result(path, expression_type)
            }
            _ => {
                let result;
                match ty.sty {
                    TyKind::Bool => {
                        result = match literal {
                            mir::interpret::ConstValue::Scalar(Scalar::Raw { data, .. }) => {
                                if *data == 0 {
                                    &ConstantDomain::False
                                } else {
                                    &ConstantDomain::True
                                }
                            }
                            _ => unreachable!(),
                        };
                    }
                    TyKind::Char => {
                        result = if let mir::interpret::ConstValue::Scalar(Scalar::Raw {
                            data,
                            ..
                        }) = literal
                        {
                            &mut self
                                .constant_value_cache
                                .get_char_for(char::try_from(*data as u32).unwrap())
                        } else {
                            unreachable!()
                        };
                    }
                    TyKind::Float(..) => {
                        result = match literal {
                            mir::interpret::ConstValue::Scalar(Scalar::Raw { data, size }) => {
                                match *size {
                                    4 => &mut self.constant_value_cache.get_f32_for(*data as u32),
                                    _ => &mut self.constant_value_cache.get_f64_for(*data as u64),
                                }
                            }
                            _ => unreachable!(),
                        };
                    }
                    TyKind::FnDef(def_id, generic_args) => {
                        result = self.visit_function_reference(def_id, ty, generic_args);
                    }
                    TyKind::Int(..) => {
                        result = match literal {
                            mir::interpret::ConstValue::Scalar(Scalar::Raw { data, size }) => {
                                let value: i128 = match *size {
                                    1 => i128::from(*data as i8),
                                    2 => i128::from(*data as i16),
                                    4 => i128::from(*data as i32),
                                    8 => i128::from(*data as i64),
                                    _ => *data as i128,
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
                        result = if let mir::interpret::ConstValue::Slice { data, start, end } =
                            literal
                        {
                            let slice = &data.bytes[*start..*end];
                            let s = std::str::from_utf8(slice).expect("non utf8 str");
                            let len_val: Rc<AbstractValue> =
                                Rc::new(ConstantDomain::U128(s.len() as u128).into());
                            let res = &mut self.constant_value_cache.get_string_for(s);

                            let path: Rc<Path> = Rc::new(
                                PathEnum::Constant {
                                    value: Rc::new(res.clone().into()),
                                }
                                .into(),
                            );
                            let len_path = Path::new_string_length(path);
                            self.current_environment.update_value_at(len_path, len_val);

                            res
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
                        if let mir::interpret::ConstValue::Scalar(Scalar::Raw { data, .. }, ..) =
                            &length.val
                        {
                            let len = *data;
                            let e_type = ExpressionType::from(&elem_type.sty);
                            if e_type != ExpressionType::U8 {
                                info!(
                                    "Untested case of mir::interpret::ConstValue::Scalar found at {:?}",
                                    self.current_span
                                );
                            }
                            match literal {
                                mir::interpret::ConstValue::Slice { data, start, end } => {
                                    let slice = &data.bytes[*start..*end];
                                    return self.deconstruct_constant_array(
                                        slice,
                                        e_type,
                                        Some(len),
                                    );
                                }
                                mir::interpret::ConstValue::ByRef { alloc, .. } => {
                                    return self.deconstruct_constant_array(
                                        &alloc.bytes,
                                        e_type,
                                        Some(len),
                                    );
                                }
                                mir::interpret::ConstValue::Scalar(
                                    mir::interpret::Scalar::Ptr(ptr),
                                ) => {
                                    let alloc =
                                        self.tcx.alloc_map.lock().unwrap_memory(ptr.alloc_id);
                                    return self.deconstruct_constant_array(
                                        &alloc.bytes,
                                        e_type,
                                        Some(len),
                                    );
                                }
                                _ => {
                                    unimplemented!("unsupported val of type Ref: {:?}", literal);
                                }
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
                    ) => match literal {
                        mir::interpret::ConstValue::Slice { data, start, end } => {
                            let slice = &data.bytes[*start..*end];
                            let e_type = ExpressionType::from(&elem_type.sty);
                            return self.deconstruct_constant_array(slice, e_type, None);
                        }
                        mir::interpret::ConstValue::ByRef { alloc, .. } => {
                            let e_type = ExpressionType::from(&elem_type.sty);
                            return self.deconstruct_constant_array(&alloc.bytes, e_type, None);
                        }
                        _ => {
                            unimplemented!("unsupported val of type Ref: {:?}", literal);
                        }
                    },
                    TyKind::Uint(..) => {
                        result = match literal {
                            mir::interpret::ConstValue::Scalar(Scalar::Raw { data, .. }) => {
                                &mut self.constant_value_cache.get_u128_for(*data)
                            }
                            _ => unreachable!(),
                        };
                    }
                    _ => {
                        println!("span: {:?}", self.current_span);
                        println!("type kind {:?}", ty.sty);
                        println!("unimplemented constant {:?}", literal);
                        result = &ConstantDomain::Unimplemented;
                    }
                };
                Rc::new(result.clone().into())
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
    #[logfn_inputs(TRACE)]
    fn deconstruct_constant_array(
        &mut self,
        bytes: &[u8],
        elem_type: ExpressionType,
        len: Option<u128>,
    ) -> Rc<AbstractValue> {
        let array_value = self.get_new_heap_address();
        if let Some(byte_len) = len {
            if byte_len > k_limits::MAX_BYTE_ARRAY_LENGTH {
                return array_value;
            }
        }
        let ordinal = if let Expression::AbstractHeapAddress(ordinal) = array_value.expression {
            ordinal
        } else {
            unreachable!()
        };
        let array_path: Rc<Path> = Rc::new(PathEnum::AbstractHeapAddress { ordinal }.into());
        let mut last_index: u128 = 0;
        for (i, operand) in self
            .get_element_values(bytes, elem_type, len)
            .into_iter()
            .enumerate()
        {
            last_index = i as u128;
            let index_value = Rc::new(
                self.constant_value_cache
                    .get_u128_for(last_index)
                    .clone()
                    .into(),
            );
            let index_path = Path::new_index(array_path.clone(), index_value);
            self.current_environment
                .update_value_at(index_path, operand);
        }
        let length_path = Path::new_length(array_path);
        let length_value = Rc::new(
            self.constant_value_cache
                .get_u128_for(last_index + 1)
                .clone()
                .into(),
        );
        self.current_environment
            .update_value_at(length_path, length_value);
        array_value
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
                    _ => unreachable!(),
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
                    _ => unreachable!(),
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
        def_id: hir::def_id::DefId,
        ty: Ty<'tcx>,
        generic_args: SubstsRef<'tcx>,
    ) -> &ConstantDomain {
        &mut self.constant_value_cache.get_function_constant_for(
            def_id,
            ty,
            generic_args,
            self.tcx,
            &mut self.summary_cache,
        )
    }

    /// Returns a Path instance that is the essentially the same as the Place instance, but which
    /// can be serialized and used as a cache key.
    #[logfn_inputs(TRACE)]
    fn visit_place(&mut self, place: &mir::Place<'tcx>) -> Rc<Path> {
        match place {
            mir::Place::Base(base_place) => match base_place {
                mir::PlaceBase::Local(local) => {
                    let result: Rc<Path> = Rc::new(
                        PathEnum::LocalVariable {
                            ordinal: local.as_usize(),
                        }
                        .into(),
                    );
                    let ty = self.get_rustc_place_type(place);
                    if let TyKind::Array(_, len) = ty {
                        let len_val = self.visit_constant(len.ty, None, &len.val);
                        let len_path = Path::new_length(result.clone());
                        self.current_environment.update_value_at(len_path, len_val);
                    }
                    result
                }
                mir::PlaceBase::Static(boxed_static) => match boxed_static.kind {
                    mir::StaticKind::Promoted(promoted) => {
                        let index = promoted.index();
                        Rc::new(PathEnum::PromotedConstant { ordinal: index }.into())
                    }
                    mir::StaticKind::Static(def_id) => {
                        let name = utils::summary_key_str(&self.tcx, def_id);
                        Rc::new(
                            PathEnum::StaticVariable {
                                def_id: Some(def_id),
                                summary_cache_key: name,
                                expression_type: self.get_place_type(place),
                            }
                            .into(),
                        )
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
                    match &base_val.expression {
                        Expression::Reference(dereferenced_path) => {
                            return dereferenced_path.clone();
                        }
                        Expression::CompileTimeConstant(ConstantDomain::Str(..)) => {
                            // A string is a reference, so fall through to wrap the string in a deref.
                            // Typically this happens because unoptimized code contains expression of
                            // the form &*"str".
                        }
                        _ => {
                            // If we are dereferencing a path whose value is not known to be a
                            // reference, we just drop the deref so that the path can be found
                            // in the environment.
                            return base.clone();
                        }
                    };
                }
                Path::new_qualified(base, Rc::new(selector))
            }
        }
    }

    /// Returns a PathSelector instance that is essentially the same as the ProjectionElem instance
    /// but which can be serialized.
    #[logfn_inputs(TRACE)]
    fn visit_projection_elem(
        &mut self,
        projection_elem: &mir::ProjectionElem<mir::Local, &rustc::ty::TyS<'tcx>>,
    ) -> PathSelector {
        match projection_elem {
            mir::ProjectionElem::Deref => PathSelector::Deref,
            mir::ProjectionElem::Field(field, _) => PathSelector::Field(field.index()),
            mir::ProjectionElem::Index(local) => {
                let local_path = Rc::new(
                    PathEnum::LocalVariable {
                        ordinal: local.as_usize(),
                    }
                    .into(),
                );
                let index_value =
                    self.lookup_path_and_refine_result(local_path, ExpressionType::Usize);
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
            mir::ProjectionElem::Subslice { from, to } => PathSelector::Subslice {
                from: *from,
                to: *to,
            },
            mir::ProjectionElem::Downcast(_, index) => PathSelector::Downcast(index.as_usize()),
        }
    }

    /// Returns an ExpressionType value corresponding to the Rustc type of the place.
    #[logfn_inputs(TRACE)]
    fn get_place_type(&mut self, place: &mir::Place<'tcx>) -> ExpressionType {
        (self.get_rustc_place_type(place)).into()
    }

    /// Returns the rustc TyKind of the given place in memory.
    #[logfn_inputs(TRACE)]
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

    /// This is a hacky and brittle way to navigate the Rust compiler's type system.
    /// Eventually it should be replaced with a comprehensive and principled mapping.
    fn get_path_rustc_type(&mut self, path: &Rc<Path>) -> &'tcx TyKind<'tcx> {
        match &path.value {
            PathEnum::LocalVariable { ordinal } => {
                let loc = &self.mir.local_decls[mir::Local::from(*ordinal)];
                &loc.ty.sty
            }
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                let t = self.get_path_rustc_type(qualifier);
                if let PathSelector::Field(ordinal) = **selector {
                    let adt = Self::get_dereferenced_type(t);
                    if let TyKind::Adt(AdtDef { variants, .. }, substs) = adt {
                        if let Some(variant_index) = variants.last() {
                            assume!(variant_index.index() == 0);
                            let variant = &variants[variant_index];
                            let field = &variant.fields[ordinal];
                            let field_ty = field.ty(*self.tcx, substs);
                            return &field_ty.sty;
                        }
                    }
                }
                info!("t is {:?}", t);
                info!("selector is {:?}", selector);
                unreachable!()
            }
            _ => {
                info!("path.value is {:?}", path.value);
                unreachable!()
            }
        }
    }

    /// Returns the target type of a reference type.
    fn get_dereferenced_type(ty: &'tcx TyKind<'tcx>) -> &'tcx TyKind<'tcx> {
        match ty {
            TyKind::Ref(_, t, _) => &t.sty,
            _ => ty,
        }
    }

    /// Returns the rustc TyKind of the element selected by projection_elem.
    #[logfn_inputs(TRACE)]
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
