// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::abstract_value::{AbstractValue, AbstractValueTrait};
use crate::block_visitor::BlockVisitor;
use crate::body_visitor::BodyVisitor;
use crate::environment::Environment;
use crate::{abstract_value, k_limits};
use itertools::Itertools;
use log_derive::*;
use mirai_annotations::*;
use rpds::HashTrieSet;
use rustc_data_structures::graph::dominators::Dominators;
use rustc_middle::mir;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Formatter, Result};
use std::rc::Rc;

pub struct FixedPointVisitor<'fixed, 'analysis, 'compilation, 'tcx, E> {
    pub bv: &'fixed mut BodyVisitor<'analysis, 'compilation, 'tcx, E>,
    already_visited: HashTrieSet<mir::BasicBlock>,
    pub block_indices: Vec<mir::BasicBlock>,
    loop_anchors: HashSet<mir::BasicBlock>,
    dominators: Dominators<mir::BasicBlock>,
    first_state: Environment,
    in_state: HashMap<mir::BasicBlock, Environment>,
    out_state: HashMap<mir::BasicBlock, Environment>,
    pub terminator_state: HashMap<mir::BasicBlock, Environment>,
}

impl<'fixed, 'analysis, 'compilation, 'tcx, E> Debug
    for FixedPointVisitor<'fixed, 'analysis, 'compilation, 'tcx, E>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "FixedPoint".fmt(f)
    }
}

/// A visitor that simply traverses enough of the MIR associated with a particular code body
/// so that we can test a call to every default implementation of the MirVisitor trait.
impl<'fixed, 'analysis, 'compilation, 'tcx, E>
    FixedPointVisitor<'fixed, 'analysis, 'compilation, 'tcx, E>
{
    #[logfn_inputs(TRACE)]
    pub fn new(
        body_visitor: &'fixed mut BodyVisitor<'analysis, 'compilation, 'tcx, E>,
        first_state: Environment,
    ) -> FixedPointVisitor<'fixed, 'analysis, 'compilation, 'tcx, E> {
        let dominators = body_visitor.mir.dominators();
        let (block_indices, loop_anchors) = get_sorted_block_indices(body_visitor.mir, &dominators);
        // in_state[bb] is the join (or widening) of the out_state values of each predecessor of bb
        let mut in_state: HashMap<mir::BasicBlock, Environment> = HashMap::new();
        // out_state[bb] is the environment that results from analyzing block bb, given in_state[bb]
        let mut out_state: HashMap<mir::BasicBlock, Environment> = HashMap::new();
        // terminator_state[bb] is the environment that should be used to error check the terminator of bb
        let mut terminator_state: HashMap<mir::BasicBlock, Environment> = HashMap::new();
        for bb in block_indices.iter() {
            in_state.insert(*bb, Environment::default());
            out_state.insert(*bb, Environment::default());
            terminator_state.insert(*bb, Environment::default());
        }
        FixedPointVisitor {
            already_visited: HashTrieSet::new(),
            bv: body_visitor,
            block_indices,
            loop_anchors,
            dominators,
            first_state,
            in_state,
            out_state,
            terminator_state,
        }
    }

    /// Visits each statement in order and then visits the terminator.
    #[logfn_inputs(TRACE)]
    pub fn visit_blocks(&mut self) {
        let blocks = self.block_indices.clone();
        for bb in blocks {
            check_for_early_break!(self.bv);
            if !self.already_visited.contains(&bb) {
                if !self.loop_anchors.contains(&bb) {
                    self.visit_basic_block(bb, 0);
                    self.out_state
                        .get_mut(&bb)
                        .expect("incorrectly initialized out_state")
                        .exit_conditions = self.bv.current_environment.exit_conditions.clone();
                } else {
                    self.compute_fixed_point(bb)
                }
            }
        }
    }

    /// Visits a single basic block, starting with an in_state that is the join of all of
    /// the out_state values of its predecessors and then updating out_state with the final
    /// current_environment of the block. Also adds the block to the already_visited set.
    #[logfn_inputs(TRACE)]
    fn visit_basic_block(&mut self, bb: mir::BasicBlock, iteration_count: usize) {
        // Merge output states of predecessors of bb
        let i_state = if iteration_count == 0 && bb.index() == 0 {
            self.first_state.clone()
        } else {
            self.get_initial_state_from_predecessors(bb, iteration_count)
        };
        self.in_state.insert(bb, i_state.clone());
        self.bv.current_environment = i_state;
        let mut block_visitor = BlockVisitor::new(self.bv);
        block_visitor.visit_basic_block(bb, &mut self.terminator_state);
        self.out_state
            .insert(bb, self.bv.current_environment.clone());
        self.already_visited = self.already_visited.insert(bb);
    }

    /// Repeatedly evaluate the loop body starting at loop_anchor until widening
    /// kicked in and a fixed point has been reached.
    #[logfn_inputs(TRACE)]
    fn compute_fixed_point(&mut self, loop_anchor: mir::BasicBlock) {
        let saved_already_visited = self.already_visited.clone();
        let saved_fresh_variable_offset = self.bv.fresh_variable_offset;
        let mut iteration_count = 1;
        let mut changed = true;
        // Iterate at least 4 times so that widening kicks in for loop variables and at least
        // one iteration was performed starting with widened variables.
        while iteration_count <= 4 || changed {
            self.already_visited = saved_already_visited.clone();
            self.bv.fresh_variable_offset = saved_fresh_variable_offset;
            changed = self.visit_loop_body(loop_anchor, iteration_count);
            check_for_early_break!(self.bv);
            if iteration_count > k_limits::MAX_FIXPOINT_ITERATIONS {
                break;
            }
            iteration_count += 1;
        }
        if iteration_count > 10 {
            warn!(
                "Fixed point loop took {} iterations for {}.",
                iteration_count, self.bv.function_name
            );
        } else {
            trace!(
                "Fixed point loop took {} iterations for {}.",
                iteration_count,
                self.bv.function_name
            );
        }
    }

    /// Visits a loop body. Return true if the out_state computed by this visit is not a subset
    /// of the out_state computed previously. When it is a subset, a fixed point has been reached.
    /// A loop body is all of the blocks that are dominated by the loop anchor.
    #[logfn_inputs(TRACE)]
    fn visit_loop_body(&mut self, loop_anchor: mir::BasicBlock, iteration_count: usize) -> bool {
        let mut changed = false;
        let blocks = self.block_indices.clone();
        for bb in blocks {
            if !self.already_visited.contains(&bb)
                && self.dominators.is_dominated_by(bb, loop_anchor)
            {
                // Visit the next block, or the entire nested loop anchored by it.
                if bb == loop_anchor {
                    self.visit_basic_block(bb, iteration_count); // join or widen
                } else if self.loop_anchors.contains(&bb) {
                    self.compute_fixed_point(bb);
                } else {
                    self.visit_basic_block(bb, 0); // conditional expressions
                }

                // Check for a fixed point.
                if !self.bv.current_environment.subset(&self.out_state[&bb]) {
                    // There is some path for which self.bv.current_environment.value_at(path) includes
                    // a value this is not present in self.out_state[bb].value_at(path), so any block
                    // that used self.out_state[bb] as part of its input state now needs to get reanalyzed.
                    changed = true;
                }
            }
        }
        changed
    }

    /// Join the exit states from all predecessors blocks to get the entry state fo this block.
    /// If a predecessor has not yet been analyzed, its state does not form part of the join.
    /// If no predecessors have been analyzed, the entry state is a default entry state with an
    /// entry condition of TOP.
    #[logfn_inputs(DEBUG)]
    fn get_initial_state_from_predecessors(
        &mut self,
        bb: mir::BasicBlock,
        iteration_count: usize,
    ) -> Environment {
        // First compute a joint state from the out states of eligible predecessors.
        // We use the exit conditions for precise joins.
        let mut predecessor_states_and_conditions: Vec<(Environment, Rc<AbstractValue>)> = self
            .bv
            .mir
            .predecessors_for(bb)
            .iter()
            .filter_map(|pred_bb| {
                let pred_state = &self.out_state[pred_bb];
                if let Some(pred_exit_condition) = pred_state.exit_conditions.get(&bb) {
                    if pred_exit_condition.as_bool_if_known().unwrap_or(true) {
                        Some((pred_state.clone(), pred_exit_condition.clone()))
                    } else {
                        // If pred_bb is known to have a false exit condition for bb it can be ignored.
                        None
                    }
                } else {
                    // If pred_state does not have an exit condition map, it is in its default state
                    // which means it has not yet been visited, or it is code that is known to always
                    // panic at runtime. Either way, we don't want to include its out state here.
                    None
                }
            })
            .collect();
        if predecessor_states_and_conditions.is_empty() {
            // bb is unreachable, at least in this iteration.
            // We therefore give it a false entry condition so that the block analyses knows
            // the block is unreachable.
            let mut initial_state = self.in_state[&bb].clone();
            initial_state.entry_condition = Rc::new(abstract_value::FALSE);
            return initial_state;
        }

        // we want to do right associative operations (for simplification purposes) and that is easier if we reverse.
        predecessor_states_and_conditions.reverse();
        let mut joined_state = predecessor_states_and_conditions
            .into_iter()
            .fold1(|(state1, cond1), (state2, cond2)| {
                if iteration_count == 0 {
                    (state2.conditional_join(state1, &cond2), cond1)
                } else if iteration_count <= 2 {
                    (state2.join(state1), cond1)
                } else {
                    // Once all paths have already been analyzed for a second time (iteration_count == 2)
                    // all blocks not involved in loops will have their final environments.
                    // The remainder will end up here from iteration 3 onwards and we need to
                    // widen in order to reach a fixed point.
                    (state2.widen(state1), cond1)
                }
            })
            .expect("one or more states to fold into something")
            .0;

        let at_loop_anchor = self.loop_anchors.contains(&bb);
        // Now we compute an entry condition from the exit conditions of the eligible predecessors
        let entry_condition = self
            .bv
            .mir
            .predecessors_for(bb)
            .iter()
            .filter_map(|pred_bb| {
                let pred_out_state = &self.out_state[pred_bb];
                let pred_exit_condition = pred_out_state.exit_conditions.get(&bb);
                if at_loop_anchor && self.dominators.is_dominated_by(*pred_bb, bb) {
                    // A block that is part of the loop body (dominated by bb, which is an anchor,
                    // as well as preceding bb) does not contribute a useful path condition
                    // since the state that may be guarded by it cannot safely be distinguished from
                    // state that was provided by non loop body predecessors.
                    // Furthermore, since loop back path conditions incorporate the initial path
                    // conditions of a loop, every fixed point iteration of the loop will expand
                    // the initial path condition, which is bad in many ways.
                    return None;
                }
                if let Some(pred_exit_condition) = pred_exit_condition {
                    if pred_exit_condition.as_bool_if_known().unwrap_or(false) {
                        // A true exit condition tells us nothing. If we are already widening,
                        // then replace the true condition with equalities from the corresponding
                        // environment.
                        Some(
                            pred_exit_condition
                                .add_equalities_for_widened_vars(pred_out_state, &joined_state),
                        )
                    } else {
                        Some(pred_exit_condition.clone())
                    }
                } else {
                    // Can happen in iteration 1 when pred_bb is a loop body block (and thus still
                    // in its default state.
                    None
                }
            })
            .fold1(|acc, cond| acc.or(cond))
            .unwrap_or_else(|| Rc::new(abstract_value::TRUE));
        joined_state.entry_condition = entry_condition;
        joined_state
    }
}

/// Do a topological sort, breaking loops by preferring lower block indices, using dominance
/// to determine if there is a loop (if a is predecessor of b and b dominates a then they
/// form a loop and we'll emit the one with the lower index first).
#[logfn_inputs(TRACE)]
fn add_predecessors_then_root_block<'analysis, 'tcx>(
    mir: mir::ReadOnlyBodyAndCache<'analysis, 'tcx>,
    root_block: mir::BasicBlock,
    dominators: &Dominators<mir::BasicBlock>,
    loop_anchors: &mut HashSet<mir::BasicBlock>,
    block_indices: &mut Vec<mir::BasicBlock>,
    already_added: &mut HashSet<mir::BasicBlock>,
) {
    if !already_added.insert(root_block) {
        return;
    }
    for pred_bb in mir.predecessors_for(root_block).iter() {
        if already_added.contains(pred_bb) {
            continue;
        };
        if dominators.is_dominated_by(*pred_bb, root_block) {
            // pred_bb has still to be added, so it has a greater index than root_block, making root_block the loop anchor.
            checked_assume!(root_block.index() < pred_bb.index());
            // Root block has a smaller index than pred_bb because it has not already been added.
            loop_anchors.insert(root_block);
            continue;
        }
        add_predecessors_then_root_block(
            mir,
            *pred_bb,
            dominators,
            loop_anchors,
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
#[logfn(TRACE)]
fn get_sorted_block_indices(
    mir: mir::ReadOnlyBodyAndCache<'_, '_>,
    dominators: &Dominators<mir::BasicBlock>,
) -> (Vec<mir::BasicBlock>, HashSet<mir::BasicBlock>) {
    let mut block_indices = Vec::new();
    let mut already_added = HashSet::new();
    let mut loop_anchors = HashSet::new();
    for bb in mir.basic_blocks().indices() {
        add_predecessors_then_root_block(
            mir,
            bb,
            &dominators,
            &mut loop_anchors,
            &mut block_indices,
            &mut already_added,
        );
    }
    (block_indices, loop_anchors)
}
