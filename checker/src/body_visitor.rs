// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::abstract_value::AbstractValue;
use crate::abstract_value::AbstractValueTrait;
use crate::constant_domain::ConstantDomain;
use crate::environment::Environment;
use crate::expression::{Expression, ExpressionType, LayoutSource};
use crate::k_limits;
use crate::options::DiagLevel;
use crate::path::PathRefinement;
use crate::path::{Path, PathEnum, PathSelector};
use crate::smt_solver::{SmtResult, SmtSolver};
use crate::summaries;
use crate::summaries::{Precondition, Summary};
use crate::tag_domain::Tag;
use crate::type_visitor::TypeVisitor;
use crate::{abstract_value, type_visitor};

use crate::block_visitor::BlockVisitor;
use crate::call_visitor::CallVisitor;
use crate::crate_visitor::CrateVisitor;
use crate::fixed_point_visitor::FixedPointVisitor;
use log_derive::*;
use mirai_annotations::*;
use rustc_errors::DiagnosticBuilder;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;
use std::fmt::{Debug, Formatter, Result};
use std::io::Write;
use std::rc::Rc;
use std::time::Instant;

/// Holds the state for the function body visitor.
pub struct BodyVisitor<'analysis, 'compilation, 'tcx, E> {
    pub cv: &'analysis mut CrateVisitor<'compilation, 'tcx>,
    pub tcx: TyCtxt<'tcx>,
    pub def_id: DefId,
    pub mir: &'tcx mir::Body<'tcx>,
    pub smt_solver: &'analysis mut dyn SmtSolver<E>,
    pub buffered_diagnostics: &'analysis mut Vec<DiagnosticBuilder<'compilation>>,
    pub active_calls_map: &'analysis mut HashMap<DefId, u64>,

    pub already_reported_errors_for_call_to: HashSet<Rc<AbstractValue>>,
    pub analyzing_static_var: bool,
    // True if the current function cannot be analyzed and hence is just assumed to be correct.
    pub assume_function_is_angelic: bool,
    pub assume_preconditions_of_next_call: bool,
    pub async_fn_summary: Option<Summary>,
    pub check_for_errors: bool,
    pub check_for_unconditional_precondition: bool,
    pub current_environment: Environment,
    pub current_location: mir::Location,
    pub current_span: rustc_span::Span,
    pub start_instant: Instant,
    pub exit_environment: Option<Environment>,
    pub function_name: Rc<String>,
    pub heap_addresses: HashMap<mir::Location, Rc<AbstractValue>>,
    pub post_condition: Option<Rc<AbstractValue>>,
    pub post_condition_block: Option<mir::BasicBlock>,
    pub preconditions: Vec<Precondition>,
    pub unwind_condition: Option<Rc<AbstractValue>>,
    pub unwind_environment: Environment,
    pub fresh_variable_offset: usize,
    pub type_visitor: TypeVisitor<'tcx>,
}

impl<'analysis, 'compilation, 'tcx, E> Debug for BodyVisitor<'analysis, 'compilation, 'tcx, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "BodyVisitor".fmt(f)
    }
}

/// A visitor that simply traverses enough of the MIR associated with a particular code body
/// so that we can test a call to every default implementation of the MirVisitor trait.
impl<'analysis, 'compilation, 'tcx, E> BodyVisitor<'analysis, 'compilation, 'tcx, E> {
    pub fn new(
        crate_visitor: &'analysis mut CrateVisitor<'compilation, 'tcx>,
        def_id: DefId,
        smt_solver: &'analysis mut dyn SmtSolver<E>,
        buffered_diagnostics: &'analysis mut Vec<DiagnosticBuilder<'compilation>>,
        active_calls_map: &'analysis mut HashMap<DefId, u64>,
    ) -> BodyVisitor<'analysis, 'compilation, 'tcx, E> {
        let function_name = crate_visitor
            .summary_cache
            .get_summary_key_for(def_id)
            .clone();
        let mir = crate_visitor.tcx.optimized_mir(def_id);
        let tcx = crate_visitor.tcx;
        BodyVisitor {
            cv: crate_visitor,
            tcx,
            def_id,
            mir,
            smt_solver,
            buffered_diagnostics,
            active_calls_map,

            already_reported_errors_for_call_to: HashSet::new(),
            analyzing_static_var: false,
            assume_function_is_angelic: false,
            assume_preconditions_of_next_call: false,
            async_fn_summary: None,
            check_for_errors: false,
            check_for_unconditional_precondition: false, // logging + new mir code gen breaks this for now
            current_environment: Environment::default(),
            current_location: mir::Location::START,
            current_span: rustc_span::DUMMY_SP,
            start_instant: Instant::now(),
            exit_environment: None,
            function_name,
            heap_addresses: HashMap::default(),
            post_condition: None,
            post_condition_block: None,
            preconditions: Vec::new(),
            unwind_condition: None,
            unwind_environment: Environment::default(),
            fresh_variable_offset: 0,
            type_visitor: TypeVisitor::new(def_id, mir, tcx),
        }
    }

    /// Restores the method only state to its initial state.
    /// Used to analyze the mir bodies of promoted constants in the context of the defining function.
    #[logfn_inputs(TRACE)]
    fn reset_visitor_state(&mut self) {
        self.already_reported_errors_for_call_to = HashSet::new();
        self.assume_function_is_angelic = false;
        self.check_for_errors = false;
        self.check_for_unconditional_precondition = false;
        self.current_environment = Environment::default();
        self.current_location = mir::Location::START;
        self.current_span = rustc_span::DUMMY_SP;
        self.start_instant = Instant::now();
        self.exit_environment = None;
        self.heap_addresses = HashMap::default();
        self.post_condition = None;
        self.post_condition_block = None;
        self.preconditions = Vec::new();
        self.unwind_condition = None;
        self.unwind_environment = Environment::default();
        self.fresh_variable_offset = 1000;
        self.type_visitor.reset_visitor_state();
    }

    /// Analyze the body and store a summary of its behavior in self.summary_cache.
    /// Returns true if the newly computed summary is different from the summary (if any)
    /// that is already in the cache.
    #[logfn_inputs(TRACE)]
    pub fn visit_body(
        &mut self,
        function_constant_args: &[(Rc<Path>, Rc<AbstractValue>)],
        parameter_types: &[Ty<'tcx>],
    ) -> Summary {
        if cfg!(DEBUG) {
            let mut stdout = std::io::stdout();
            stdout.write_fmt(format_args!("{:?}", self.def_id)).unwrap();
            rustc_mir::util::write_mir_pretty(self.tcx, Some(self.def_id), &mut stdout).unwrap();
            info!("{:?}", stdout.flush());
        }
        *self.active_calls_map.entry(self.def_id).or_insert(0) += 1;
        let saved_heap_counter = self.cv.constant_value_cache.swap_heap_counter(0);

        // The entry block has no predecessors and its initial state is the function parameters
        // (which we omit here so that we can lazily provision them with additional context)
        // as well any promoted constants.
        let mut first_state = self.promote_constants();

        // Add parameter values that are function constants.
        // Also add entries for closure fields.
        for (path, val) in function_constant_args.iter() {
            TypeVisitor::add_any_closure_fields_for(
                &mut self.current_environment,
                parameter_types,
                &mut first_state,
                &path,
            );
            first_state.value_map.insert_mut(path.clone(), val.clone());
        }

        // Update the current environment
        let mut fixed_point_visitor = FixedPointVisitor::new(self, first_state);
        fixed_point_visitor.visit_blocks();

        let elapsed_time_in_seconds = fixed_point_visitor.bv.start_instant.elapsed().as_secs();
        if elapsed_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
            fixed_point_visitor
                .bv
                .report_timeout(elapsed_time_in_seconds);
        }
        let mut result = Summary::default();
        result.is_computed = true; // Otherwise this function keeps getting re-analyzed
        result.is_angelic = true; // Callers have to make possibly false assumptions.
        if !fixed_point_visitor.bv.assume_function_is_angelic {
            // Now traverse the blocks again, doing checks and emitting diagnostics.
            // terminator_state[bb] is now complete for every basic block bb in the body.
            fixed_point_visitor.bv.check_for_errors(
                &fixed_point_visitor.block_indices,
                &mut fixed_point_visitor.terminator_state,
            );
            let entry = self
                .active_calls_map
                .entry(self.def_id)
                .or_insert_with(|| unreachable!());
            if *entry == 1 {
                self.active_calls_map.remove(&self.def_id);
            } else {
                *entry -= 1;
            }
            let elapsed_time_in_seconds = self.start_instant.elapsed().as_secs();
            if elapsed_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
                self.report_timeout(elapsed_time_in_seconds);
            } else {
                // Now create a summary of the body that can be in-lined into call sites.
                if self.async_fn_summary.is_some() {
                    self.preconditions = self.translate_async_preconditions();
                    // todo: also translate side-effects, return result and post-condition
                };

                result = summaries::summarize(
                    self.mir.arg_count,
                    self.exit_environment.as_ref(),
                    &self.preconditions,
                    &self.post_condition,
                    self.unwind_condition.clone(),
                    &self.unwind_environment,
                    self.tcx,
                );
            }
        }
        self.cv
            .constant_value_cache
            .swap_heap_counter(saved_heap_counter);

        result
    }

    fn report_timeout(&mut self, elapsed_time_in_seconds: u64) {
        // This body is beyond MIRAI for now
        if self.cv.options.diag_level != DiagLevel::RELAXED {
            let warning = self
                .cv
                .session
                .struct_span_warn(self.current_span, "The analysis of this function timed out");
            self.emit_diagnostic(warning);
        }
        warn!(
            "analysis of {} timed out after {} seconds",
            self.function_name, elapsed_time_in_seconds,
        );
        let call_entry = self.active_calls_map.entry(self.def_id).or_insert(0);
        if *call_entry > 1 {
            *call_entry -= 1;
        } else {
            self.active_calls_map.remove(&self.def_id);
        }
        self.assume_function_is_angelic = true;
    }

    /// Adds the given diagnostic builder to the buffer.
    /// Buffering diagnostics gives us the chance to sort them before printing them out,
    /// which is desirable for tools that compare the diagnostics from one run of MIRAI with another.
    #[logfn_inputs(TRACE)]
    pub fn emit_diagnostic(&mut self, mut diagnostic_builder: DiagnosticBuilder<'compilation>) {
        precondition!(self.check_for_errors);
        if !self.def_id.is_local() && !matches!(self.cv.options.diag_level, DiagLevel::PARANOID) {
            // only give diagnostics in code that belongs to the crate being analyzed
            diagnostic_builder.cancel();
            return;
        }
        // Do not emit diagnostics for code generated by derive macros since it is currently
        // unlikely that the end user of the diagnostic will be able to anything about it.
        use rustc_span::hygiene::{ExpnData, ExpnKind, MacroKind};
        if let [span] = &diagnostic_builder.span.primary_spans() {
            if let Some(ExpnData {
                kind: ExpnKind::Macro(MacroKind::Derive, ..),
                ..
            }) = span.source_callee()
            {
                info!("derive macro has warning: {:?}", diagnostic_builder);
                diagnostic_builder.cancel();
                return;
            }
        }
        self.buffered_diagnostics.push(diagnostic_builder);
    }

    pub fn get_i128_const_val(&mut self, val: i128) -> Rc<AbstractValue> {
        Rc::new(
            self.cv
                .constant_value_cache
                .get_i128_for(val)
                .clone()
                .into(),
        )
    }

    pub fn get_u128_const_val(&mut self, val: u128) -> Rc<AbstractValue> {
        Rc::new(
            self.cv
                .constant_value_cache
                .get_u128_for(val)
                .clone()
                .into(),
        )
    }

    /// Use the local and global environments to resolve Path to an abstract value.
    #[logfn_inputs(TRACE)]
    pub fn lookup_path_and_refine_result(
        &mut self,
        path: Rc<Path>,
        result_rustc_type: Ty<'tcx>,
    ) -> Rc<AbstractValue> {
        let result_type: ExpressionType = (&result_rustc_type.kind).into();
        match &path.value {
            PathEnum::Alias { value } | PathEnum::Offset { value } => {
                return value.clone();
            }
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } if matches!(selector.as_ref(), PathSelector::Deref) => {
                let path = Path::new_qualified(
                    qualifier.clone(),
                    Rc::new(PathSelector::Index(Rc::new(0u128.into()))),
                );
                if self.current_environment.value_map.contains_key(&path) {
                    let refined_val = self.lookup_path_and_refine_result(path, result_rustc_type);
                    if !refined_val.is_bottom() {
                        return refined_val;
                    }
                }
            }
            _ => {}
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
        let result = if refined_val.is_bottom() || refined_val.is_top() {
            if self.imported_root_static(&path) {
                return self.lookup_path_and_refine_result(path, result_rustc_type);
            }
            if path.path_length() < k_limits::MAX_PATH_LENGTH {
                let mut result = None;
                if let PathEnum::QualifiedPath {
                    qualifier,
                    selector,
                    ..
                } = &path.value
                {
                    if matches!(
                        *selector.as_ref(),
                        PathSelector::Deref | PathSelector::Index(..)
                    ) {
                        if let PathSelector::Index(index_val) = selector.as_ref() {
                            //todo: this step is O(n) which makes the analysis O(n**2) when there
                            //are a bunch of statics in the code.
                            //An example of this is https://doc-internal.dalek.rs/develop/src/curve25519_dalek/backend/serial/u64/constants.rs.html#143
                            result = self.lookup_weak_value(qualifier, index_val);
                        }
                        if result.is_none() && result_type.is_integer() {
                            let qualifier_val = self.lookup_path_and_refine_result(
                                qualifier.clone(),
                                ExpressionType::NonPrimitive.as_rustc_type(self.tcx),
                            );
                            if qualifier_val.is_contained_in_zeroed_heap_block() {
                                result = Some(if result_type.is_signed_integer() {
                                    self.get_i128_const_val(0)
                                } else {
                                    self.get_u128_const_val(0)
                                })
                            }
                        }
                    }
                }
                result.unwrap_or_else(|| {
                    let result = match &path.value {
                        PathEnum::HeapBlock { value } => {
                            if let Expression::HeapBlock { is_zeroed, .. } = value.expression {
                                if is_zeroed {
                                    if result_type.is_signed_integer() {
                                        return self.get_i128_const_val(0);
                                    } else if result_type.is_unsigned_integer() {
                                        return self.get_u128_const_val(0);
                                    }
                                }
                            }
                            AbstractValue::make_typed_unknown(result_type.clone(), path.clone())
                        }
                        PathEnum::LocalVariable { .. } if !refined_val.is_top() => refined_val,
                        _ => AbstractValue::make_typed_unknown(
                            result_type.clone(),
                            path.replace_parameter_root_with_copy(),
                        ),
                    };
                    if result_type != ExpressionType::NonPrimitive {
                        self.current_environment
                            .update_value_at(path, result.clone());
                    }
                    result
                })
            } else {
                let result = if let PathEnum::LocalVariable { .. } = path.value {
                    refined_val
                } else {
                    AbstractValue::make_typed_unknown(
                        result_type.clone(),
                        path.replace_parameter_root_with_copy(),
                    )
                };
                if result_type != ExpressionType::NonPrimitive {
                    self.current_environment
                        .update_value_at(path, result.clone());
                }
                result
            }
        } else {
            refined_val
        };
        if result_type == ExpressionType::Bool
            && self.current_environment.entry_condition.implies(&result)
        {
            return Rc::new(abstract_value::TRUE);
        }
        let expression_type = result.expression.infer_type();
        if (result_type != ExpressionType::ThinPointer
            && result_type != ExpressionType::NonPrimitive)
            && (expression_type == ExpressionType::ThinPointer
                || expression_type == ExpressionType::NonPrimitive)
        {
            result.dereference(result_type)
        } else {
            result
        }
    }

    /// If there is a path of the form key_qualifier[0..n] = v then return v.
    /// todo: if there are paths of the form key_qualifier[i] = vi where we could have i == key_index
    /// at runtime, then return a conditional expression that uses v as the default value (if there
    /// is a [0..n] path, otherwise zero or unknown).
    #[logfn_inputs(TRACE)]
    fn lookup_weak_value(
        &mut self,
        key_qualifier: &Rc<Path>,
        _key_index: &Rc<AbstractValue>,
    ) -> Option<Rc<AbstractValue>> {
        if self.analyzing_static_var {
            return None;
        }
        for (path, value) in self.current_environment.value_map.iter() {
            if let PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } = &path.value
            {
                if let PathSelector::Slice(..) = selector.as_ref() {
                    if value.expression.infer_type().is_primitive() && key_qualifier.eq(qualifier) {
                        // This is the supported case for arrays constructed via a repeat expression.
                        // We assume that index is in range since that has already been checked.
                        // todo: deal with the case where there is another path that aliases the slice.
                        // i.e. a situation that arises if a repeat initialized array has been updated
                        // with an index that is not an exact match for key_index.
                        return Some(value.clone());
                    }
                }
                // todo: deal with PathSelector::Index when there is a possibility that
                // key_index might match it at runtime.
            }
        }
        None
    }

    /// Returns true if the given path is rooted in a static that has not yet been imported.
    /// Also imports the static in that case, so looking up the path again when this returns
    /// true is the thing to do.
    #[logfn_inputs(TRACE)]
    pub fn imported_root_static(&mut self, path: &Rc<Path>) -> bool {
        if let PathEnum::StaticVariable {
            def_id,
            summary_cache_key,
            expression_type,
        } = &path.value
        {
            if self.current_environment.value_map.contains_key(path) {
                return false;
            }
            self.current_environment.update_value_at(
                path.clone(),
                AbstractValue::make_typed_unknown(expression_type.clone(), path.clone()),
            );
            if self.imported_static(&path, *def_id, summary_cache_key) {
                return true;
            }
        }
        if let PathEnum::QualifiedPath { qualifier, .. } = &path.value {
            self.imported_root_static(qualifier)
        } else {
            false
        }
    }

    /// Gets the value of the given static variable by obtaining a summary for the corresponding def_id.
    #[logfn_inputs(TRACE)]
    fn imported_static(
        &mut self,
        path: &Rc<Path>,
        def_id: Option<DefId>,
        summary_cache_key: &Rc<String>,
    ) -> bool {
        let environment_before_call = self.current_environment.clone();
        let saved_analyzing_static_var = self.analyzing_static_var;
        self.analyzing_static_var = true;
        let mut block_visitor;
        let summary;
        let summary = if let Some(def_id) = def_id {
            let generic_args = self.cv.substs_cache.get(&def_id).cloned();
            let callee_generic_argument_map = if let Some(generic_args) = generic_args {
                self.type_visitor
                    .get_generic_arguments_map(def_id, generic_args, &[])
            } else {
                None
            };
            let ty = self.tcx.type_of(def_id);
            let func_const = self
                .cv
                .constant_value_cache
                .get_function_constant_for(
                    def_id,
                    ty,
                    generic_args.unwrap_or_else(|| self.tcx.empty_substs_for_def_id(def_id)),
                    self.tcx,
                    &mut self.cv.known_names_cache,
                    &mut self.cv.summary_cache,
                )
                .clone();
            block_visitor = BlockVisitor::new(self);
            let mut call_visitor = CallVisitor::<E>::new(
                &mut block_visitor,
                def_id,
                generic_args,
                callee_generic_argument_map,
                environment_before_call,
                func_const,
            );
            let func_ref = call_visitor
                .callee_func_ref
                .clone()
                .expect("CallVisitor::new should guarantee this");
            let cached_summary = call_visitor
                .block_visitor
                .bv
                .cv
                .summary_cache
                .get_summary_for_call_site(&func_ref, None);
            if cached_summary.is_computed {
                cached_summary
            } else {
                summary = call_visitor.create_and_cache_function_summary();
                &summary
            }
        } else {
            summary = self
                .cv
                .summary_cache
                .get_persistent_summary_for(summary_cache_key);
            &summary
        };
        if summary.is_computed && !summary.side_effects.is_empty() {
            let side_effects = summary.side_effects.clone();
            self.fresh_variable_offset += 1_000_000;
            // Effects on the path
            let environment = self.current_environment.clone();
            self.transfer_and_refine(
                &side_effects,
                path.clone(),
                &Path::new_result(),
                &None,
                &[],
                &environment,
            );
            // Effects on the heap
            for (path, value) in side_effects.iter() {
                if path.is_rooted_by_abstract_heap_block() {
                    self.current_environment.update_value_at(
                        path.refine_parameters(
                            &[],
                            &None,
                            &self.current_environment,
                            self.fresh_variable_offset,
                        ),
                        value.refine_parameters(
                            &[],
                            &None,
                            &self.current_environment,
                            self.fresh_variable_offset,
                        ),
                    );
                }
            }
            self.analyzing_static_var = saved_analyzing_static_var;
            true
        } else {
            self.analyzing_static_var = saved_analyzing_static_var;
            false
        }
    }

    /// self.async_fn_summary is a summary of the closure that results from rewriting
    /// the current function body into a generator. The preconditions found in this
    /// summary are expressed in terms of the closure fields that capture the parameters
    /// of the current function. The pre-conditions are also governed by a path condition
    /// that requires the closure (enum) to be in state 0 (have a discriminant value of 0).
    /// This function rewrites the pre-conditions to instead refer to the parameters of the
    /// current function and eliminates the condition based on the closure discriminant value.
    fn translate_async_preconditions(&mut self) -> Vec<Precondition> {
        // In order to specialize the closure preconditions to the current context,
        // we need to allocate a closure object from the heap and to populate its fields
        // with the (unknown) values of the parameters and locals of the current context.

        // The byte size of the closure object is not used, so we just fake it.
        let zero: Rc<AbstractValue> = Rc::new(0u128.into());
        let closure_object = self.get_new_heap_block(
            zero.clone(),
            zero,
            false,
            self.tcx.types.trait_object_dummy_self,
        );
        let closure_path: Rc<Path> = match &closure_object.expression {
            Expression::HeapBlock { .. } => Rc::new(
                PathEnum::HeapBlock {
                    value: closure_object.clone(),
                }
                .into(),
            ),
            _ => assume_unreachable!(),
        };

        // Setting the discriminant to 0 allows the related conditions in the closure's preconditions
        // to get simplified away.
        let discriminant = Path::new_discriminant(
            Path::new_field(closure_path.clone(), 0).refine_paths(&self.current_environment),
        );
        let discriminant_val = self.get_u128_const_val(0);

        // Populate the closure object fields with the parameters and locals of the current context.
        self.current_environment
            .update_value_at(discriminant, discriminant_val);
        for (i, loc) in self.mir.local_decls.iter().skip(1).enumerate() {
            let qualifier = closure_path.clone();
            let closure_path = Path::new_field(Path::new_field(qualifier, 0), i)
                .refine_paths(&self.current_environment);
            // skip(1) above ensures this
            assume!(i < usize::max_value());
            let path = if i < self.mir.arg_count {
                Path::new_parameter(i + 1)
            } else {
                Path::new_local(i + 1)
            };
            let specialized_type = self
                .type_visitor
                .specialize_generic_argument_type(loc.ty, &self.type_visitor.generic_argument_map);
            let value = self.lookup_path_and_refine_result(path, specialized_type);
            self.current_environment
                .update_value_at(closure_path, value);
        }

        // Now set up the dummy closure object as the actual argument used to specialize
        // the summary of the closure function.
        let actual_args = vec![(closure_path, closure_object)];

        // Now specialize/refine the closure summary's preconditions so that they can be used
        // as the preconditions of the current function (from which the closure function was
        // derived when turning it into a generator).
        self.async_fn_summary
            .as_ref()
            .unwrap()
            .preconditions
            .iter()
            .map(|precondition| {
                let refined_condition = precondition
                    .condition
                    .refine_parameters(
                        &actual_args,
                        &None,
                        &self.current_environment,
                        self.fresh_variable_offset,
                    )
                    .refine_paths(&self.current_environment);
                Precondition {
                    condition: refined_condition,
                    message: precondition.message.clone(),
                    provenance: precondition.provenance.clone(),
                    spans: precondition.spans.clone(),
                }
            })
            .collect()
    }

    #[logfn_inputs(TRACE)]
    fn check_for_errors(
        &mut self,
        block_indices: &[mir::BasicBlock],
        terminator_state: &mut HashMap<mir::BasicBlock, Environment>,
    ) {
        self.check_for_errors = true;
        for bb in block_indices.iter() {
            let t_state = (&terminator_state[bb]).clone();
            self.current_environment = t_state;
            self.visit_basic_block(*bb, terminator_state);
        }
        if self.exit_environment.is_none() {
            // Can only happen if there has been no return statement in the body,
            // which only happens if there is no way for the function to return to its
            // caller. We model this as a false post condition.
            self.post_condition = Some(Rc::new(abstract_value::FALSE));
        }
    }

    /// Use the visitor to compute the state corresponding to promoted constants.
    #[logfn_inputs(TRACE)]
    fn promote_constants(&mut self) -> Environment {
        let mut environment = Environment::default();
        let saved_mir = self.mir;
        for (ordinal, constant_mir) in self.tcx.promoted_mir(self.def_id).iter().enumerate() {
            self.mir = constant_mir;
            self.type_visitor.mir = self.mir;
            let result_rustc_type = self.mir.local_decls[mir::Local::from(0usize)].ty;
            self.visit_promoted_constants_block();
            if self.exit_environment.is_some() {
                let mut result_root: Rc<Path> = Path::new_result();
                let mut promoted_root: Rc<Path> =
                    Rc::new(PathEnum::PromotedConstant { ordinal }.into());
                if self
                    .type_visitor
                    .starts_with_slice_pointer(&result_rustc_type.kind)
                {
                    let source_length_path = Path::new_length(result_root.clone());
                    let length_val = self
                        .exit_environment
                        .as_ref()
                        .unwrap()
                        .value_map
                        .get(&source_length_path)
                        .expect("collection to have a length");
                    let target_length_path = Path::new_length(promoted_root.clone());
                    environment.update_value_at(target_length_path, length_val.clone());
                    promoted_root = Path::new_field(promoted_root, 0);
                    result_root = Path::new_field(result_root, 0);
                }
                //todo: probably should use exit environment and probably should expect a value
                let value =
                    self.lookup_path_and_refine_result(result_root.clone(), result_rustc_type);
                match &value.expression {
                    Expression::HeapBlock { .. } => {
                        let heap_root: Rc<Path> = Rc::new(
                            PathEnum::HeapBlock {
                                value: value.clone(),
                            }
                            .into(),
                        );
                        for (path, value) in self
                            .exit_environment
                            .as_ref()
                            .unwrap()
                            .value_map
                            .iter()
                            .filter(|(p, _)| p.is_rooted_by(&heap_root))
                        {
                            environment.update_value_at(path.clone(), value.clone());
                        }
                        environment.update_value_at(promoted_root.clone(), value.clone());
                    }
                    Expression::Reference(local_path) => {
                        self.promote_reference(
                            &mut environment,
                            result_rustc_type,
                            &promoted_root,
                            local_path,
                            ordinal,
                        );
                    }
                    _ => {
                        for (path, value) in self
                            .exit_environment
                            .as_ref()
                            .unwrap()
                            .value_map
                            .iter()
                            .filter(|(p, _)| p.is_rooted_by(&result_root))
                        {
                            let promoted_path =
                                path.replace_root(&result_root, promoted_root.clone());
                            environment.update_value_at(promoted_path, value.clone());
                        }
                        if let Expression::Variable { .. } = &value.expression {
                            // The constant is a stack allocated struct. No need for a separate entry.
                        } else {
                            environment.update_value_at(promoted_root.clone(), value.clone());
                        }
                    }
                }
            }
            self.reset_visitor_state();
        }
        self.mir = saved_mir;
        self.type_visitor.mir = saved_mir;
        environment
    }

    /// local_path is reference to a local of the promoted constant function.
    /// Unlike other locals, it appears that the life time of promoted constant
    /// function local can exceed the life time of the of promoted constant function
    /// and even the function that hosts it.
    fn promote_reference(
        &mut self,
        environment: &mut Environment,
        result_rustc_type: Ty<'tcx>,
        promoted_root: &Rc<Path>,
        local_path: &Rc<Path>,
        mut ordinal: usize,
    ) {
        let target_type = type_visitor::get_target_type(result_rustc_type);
        if ExpressionType::from(&target_type.kind).is_primitive() {
            // Kind of weird, but seems to be generated for debugging support.
            // Move the value into an alias path, so that we can drop the reference to the soon to be dead local.
            let target_value = self
                .exit_environment
                .as_ref()
                .unwrap()
                .value_map
                .get(local_path)
                .expect("expect reference target to have a value");
            let value_path = Path::get_as_path(target_value.clone());
            let promoted_value = AbstractValue::make_from(Expression::Reference(value_path), 1);
            environment.update_value_at(promoted_root.clone(), promoted_value);
        } else if let TyKind::Ref(_, ty, _) = &target_type.kind {
            // Really weird. Promoting a reference to a reference. Seems to be there for debugging.
            // We see it for constant strings, so kind of like primitive values.
            ordinal += 99;
            let value_path: Rc<Path> = Rc::new(PathEnum::PromotedConstant { ordinal }.into());
            self.promote_reference(environment, ty, &value_path, local_path, ordinal);
            let promoted_value = AbstractValue::make_from(Expression::Reference(value_path), 1);
            environment.update_value_at(promoted_root.clone(), promoted_value);
        } else {
            // A composite value needs to get to get promoted to the heap
            // in order to propagate it via function summaries.
            let byte_size = self.type_visitor.get_type_size(target_type);
            let byte_size_value = self.get_u128_const_val(byte_size as u128);
            let elem_size = self
                .type_visitor
                .get_type_size(type_visitor::get_element_type(target_type));
            let alignment: Rc<AbstractValue> = Rc::new(
                (match elem_size {
                    0 => 1,
                    1 | 2 | 4 | 8 => elem_size,
                    _ => 8,
                } as u128)
                    .into(),
            );
            let heap_value =
                self.get_new_heap_block(byte_size_value, alignment, false, target_type);
            let heap_root = Path::get_as_path(heap_value);
            for (path, value) in self
                .exit_environment
                .as_ref()
                .unwrap()
                .value_map
                .iter()
                .filter(|(p, _)| (*p) == local_path || p.is_rooted_by(local_path))
            {
                let renamed_path = path.replace_root(local_path, heap_root.clone());
                environment.update_value_at(renamed_path, value.clone());
            }
            let thin_pointer_to_heap = AbstractValue::make_reference(heap_root);
            if type_visitor::is_slice_pointer(&target_type.kind) {
                let promoted_thin_pointer_path = Path::new_field(promoted_root.clone(), 0);
                environment.update_value_at(promoted_thin_pointer_path, thin_pointer_to_heap);
                let length_value = self
                    .exit_environment
                    .as_ref()
                    .unwrap()
                    .value_map
                    .get(&Path::new_length(local_path.clone()))
                    .unwrap_or_else(|| assume_unreachable!("promoted constant slice source is expected to have a length value, see source at {:?}", self.current_span))
                    .clone();
                let length_path = Path::new_length(promoted_root.clone());
                environment.update_value_at(length_path, length_value);
            } else {
                environment.update_value_at(promoted_root.clone(), thin_pointer_to_heap);
            }
        }
    }

    /// Computes a fixed point over the blocks of the MIR for a promoted constant block
    #[logfn_inputs(TRACE)]
    fn visit_promoted_constants_block(&mut self) {
        let mut fixed_point_visitor = FixedPointVisitor::new(self, Environment::default());
        fixed_point_visitor.visit_blocks();

        fixed_point_visitor.bv.check_for_errors(
            &fixed_point_visitor.block_indices,
            &mut fixed_point_visitor.terminator_state,
        );
    }

    /// Visits each statement in order and then visits the terminator.
    #[logfn_inputs(TRACE)]
    fn visit_basic_block(
        &mut self,
        bb: mir::BasicBlock,
        terminator_state: &mut HashMap<mir::BasicBlock, Environment>,
    ) {
        let mut block_visitor = BlockVisitor::new(self);
        block_visitor.visit_basic_block(bb, terminator_state)
    }

    /// Checks that the offset is either in bounds or one byte past the end of an allocated object.
    #[logfn_inputs(TRACE)]
    pub fn check_offset(&mut self, offset: &AbstractValue) {
        if let Expression::Offset { left, right, .. } = &offset.expression {
            let ge_zero = right.greater_or_equal(Rc::new(ConstantDomain::I128(0).into()));
            let mut len = left.clone();
            if let Expression::Reference(path) = &left.expression {
                if matches!(&path.value, PathEnum::HeapBlock{..}) {
                    let layout_path = Path::new_layout(path.clone());
                    if let Expression::HeapBlockLayout { length, .. } = &self
                        .lookup_path_and_refine_result(
                            layout_path,
                            ExpressionType::NonPrimitive.as_rustc_type(self.tcx),
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
            let (in_range_as_bool, entry_cond_as_bool) =
                self.check_condition_value_and_reachability(&in_range);
            //todo: eventually give a warning if in_range_as_bool is unknown. For now, that is too noisy.
            if entry_cond_as_bool.unwrap_or(true) && !in_range_as_bool.unwrap_or(true) {
                let span = self.current_span;
                let message = "effective offset is outside allocated range";
                let warning = self.cv.session.struct_span_warn(span, message);
                self.emit_diagnostic(warning);
            }
        }
    }

    /// Returns true if the function being analyzed is an analysis root.
    #[logfn_inputs(TRACE)]
    pub fn function_being_analyzed_is_root(&mut self) -> bool {
        self.active_calls_map.get(&self.def_id).unwrap_or(&0).eq(&1)
            && self.active_calls_map.values().sum::<u64>() == 1u64
    }

    /// Adds a (rpath, rvalue) pair to the current environment for every pair in effects
    /// for which the path is rooted by source_path and where rpath is path re-rooted with
    /// target_path and rvalue is value refined by replacing all occurrences of parameter values
    /// with the corresponding actual values.
    /// The effects are refined in the context of the pre_environment
    /// (the environment before the call executed), while the refined effects are applied to the
    /// current state.
    #[logfn_inputs(TRACE)]
    pub fn transfer_and_refine(
        &mut self,
        effects: &[(Rc<Path>, Rc<AbstractValue>)],
        target_path: Rc<Path>,
        source_path: &Rc<Path>,
        result_path: &Option<Rc<Path>>,
        arguments: &[(Rc<Path>, Rc<AbstractValue>)],
        pre_environment: &Environment,
    ) {
        let target_type = self
            .type_visitor
            .get_path_rustc_type(&target_path, self.current_span);
        let target_is_thin_pointer = type_visitor::is_thin_pointer(&target_type.kind);
        for (path, value) in effects
            .iter()
            .filter(|(p, _)| (*p) == *source_path || p.is_rooted_by(source_path))
        {
            trace!("effect {:?} {:?}", path, value);
            let dummy_root = Path::new_local(999_999);
            let refined_dummy_root = Path::new_local(self.fresh_variable_offset + 999_999);
            let mut tpath = path
                .replace_root(source_path, dummy_root)
                .refine_parameters(
                    arguments,
                    result_path,
                    pre_environment,
                    self.fresh_variable_offset,
                )
                .replace_root(&refined_dummy_root, target_path.clone())
                .refine_paths(pre_environment);
            let pre_state_value = self.current_environment.value_at(&tpath);
            if matches!(pre_state_value, Some(v) if v.is_widened()) {
                // If the value is self referential, i.e. if its new value refers to its old
                // value, widening may not converge. So just stick with the already widened value.
                continue;
            }
            let uncanonicalized_rvalue = value.refine_parameters(
                arguments,
                result_path,
                pre_environment,
                self.fresh_variable_offset,
            );
            let mut rvalue = uncanonicalized_rvalue.refine_paths(pre_environment);
            if let Expression::Variable { path, .. } = &uncanonicalized_rvalue.expression {
                // If the path contains a root that is a static, this will import the static into
                // the calling scope.
                if self.imported_root_static(path) {
                    rvalue = uncanonicalized_rvalue.refine_paths(&self.current_environment);
                }
            }
            trace!("refined effect {:?} {:?}", tpath, rvalue);
            let rtype = rvalue.expression.infer_type();
            match &rvalue.expression {
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
                                        result_path,
                                        pre_environment,
                                        self.fresh_variable_offset,
                                    )
                                    .refine_paths(&self.current_environment);
                                self.update_zeroed_flag_for_heap_block_from_environment(
                                    &tpath,
                                    &realloc_layout_val.expression,
                                );
                            }
                        }
                        _ => {}
                    }
                    self.current_environment.update_value_at(tpath, rvalue);
                    continue;
                }
                Expression::Join { left, right, .. } => {
                    // Refinement did not update the path since it is not known to it
                    rvalue = left.join(right.clone(), &tpath);
                }
                Expression::Offset { .. } => {
                    if self.check_for_errors && self.function_being_analyzed_is_root() {
                        self.check_offset(&rvalue);
                    }
                }
                Expression::Reference(path) => {
                    let deref_type = self
                        .type_visitor
                        .get_path_rustc_type(&tpath, self.current_span);
                    if self
                        .type_visitor
                        .starts_with_slice_pointer(&deref_type.kind)
                    {
                        if let PathEnum::QualifiedPath { selector, .. } = &tpath.value {
                            if matches!(selector.as_ref(), PathSelector::Field(0)) {
                                // tpath = qualifier.0 and rvalue = &path, so thin pointer copy
                                self.current_environment.update_value_at(tpath, rvalue);
                                continue;
                            }
                        }
                        // transferring a (pointer, length) tuple.
                        self.copy_or_move_elements(tpath.clone(), path.clone(), deref_type, false);
                        continue;
                    }
                    if target_is_thin_pointer && deref_type == self.tcx.types.never {
                        // This can happen if the result of the called function is actually a slice pointer
                        // that is being implicitly cast to a thin pointer. In that case, tpath needs
                        // to drop the field 0 bit.
                        if let PathEnum::QualifiedPath {
                            qualifier,
                            selector,
                            ..
                        } = &tpath.value
                        {
                            match selector.as_ref() {
                                PathSelector::Field(0) | PathSelector::UnionField { .. } => {
                                    // assign the pointer field of the slice pointer to the unqualified target
                                    tpath = qualifier.clone();
                                }
                                PathSelector::Field(1) => {
                                    // drop the assignment of the length field
                                    continue;
                                }
                                _ => assume_unreachable!("something went wrong here"),
                            }
                        }
                    }
                }
                Expression::RefinedParameterCopy { .. } => {
                    self.current_environment.update_value_at(tpath, rvalue);
                    continue;
                }
                Expression::UninterpretedCall {
                    callee,
                    arguments,
                    result_type,
                    ..
                } => {
                    rvalue = callee.uninterpreted_call(
                        arguments.clone(),
                        result_type.clone(),
                        tpath.clone(),
                    );
                }
                Expression::Variable { path, var_type } => {
                    if matches!(&path.value, PathEnum::PhantomData) {
                        continue;
                    }
                    let target_type = self
                        .type_visitor
                        .get_path_rustc_type(&tpath, self.current_span);
                    if let PathEnum::LocalVariable { ordinal } = &path.value {
                        if *ordinal >= self.fresh_variable_offset {
                            // A fresh variable from the callee adds no information that is not
                            // already inherent in the target location.
                            self.current_environment.value_map =
                                self.current_environment.value_map.remove(&tpath);
                            continue;
                        }
                        if rtype == ExpressionType::NonPrimitive {
                            self.copy_or_move_elements(
                                tpath.clone(),
                                path.clone(),
                                target_type,
                                false,
                            );
                        }
                    } else if path.is_rooted_by_parameter() {
                        let cpath = path.replace_parameter_root_with_copy();
                        rvalue = AbstractValue::make_typed_unknown(var_type.clone(), cpath);
                        // todo: investigate test failures that happen when removing the next two lines
                        self.current_environment.update_value_at(tpath, rvalue);
                        continue;
                    } else if rtype == ExpressionType::NonPrimitive {
                        self.copy_or_move_elements(tpath.clone(), path.clone(), target_type, false);
                    }
                }
                Expression::Widen { operand, .. } => {
                    // Refinement did not update the path since it is not known to it
                    rvalue = operand.widen(&tpath);
                }
                _ => {}
            }
            // todo: need to call copy_or_move_elements if any selector in tpath is a slice or index
            if let PathEnum::QualifiedPath { selector, .. } = &tpath.value {
                if let PathSelector::Slice(..) | PathSelector::Index(..) = selector.as_ref() {
                    let source_path = Path::get_as_path(rvalue.clone());
                    let target_type = type_visitor::get_element_type(
                        self.type_visitor
                            .get_path_rustc_type(&target_path, self.current_span),
                    );
                    self.copy_or_move_elements(tpath.clone(), source_path, target_type, false);
                    continue;
                }
            }
            if rtype != ExpressionType::NonPrimitive {
                // If tpath is a tag field path, we need to propagate the tags recorded in rvalue
                // to those paths rooted by the qualifier of tpath properly.
                if let PathEnum::QualifiedPath {
                    qualifier,
                    selector,
                    ..
                } = &tpath.value
                {
                    if **selector == PathSelector::TagField {
                        let qualifier_rustc_type = self
                            .type_visitor
                            .get_path_rustc_type(qualifier, self.current_span);
                        self.transfer_and_propagate_tags(&rvalue, qualifier, qualifier_rustc_type);
                        continue;
                    }
                }

                self.current_environment.update_value_at(tpath, rvalue);
            }
            check_for_early_return!(self);
        }
    }

    /// When we transfer a side effect of the form (root_path.$tags, tag_field_value), i.e., the callee
    /// has attached some tags to the value located at root_path, we go through all the tags recorded in
    /// tag_field_value, and invoke `attach_tag_to_elements` to properly propagate tags to elements rooted
    /// by root_path.
    #[logfn_inputs(TRACE)]
    fn transfer_and_propagate_tags(
        &mut self,
        tag_field_value: &Rc<AbstractValue>,
        root_path: &Rc<Path>,
        root_rustc_type: Ty<'tcx>,
    ) {
        if let Expression::TaggedExpression { tag, operand } = &tag_field_value.expression {
            self.transfer_and_propagate_tags(operand, root_path, root_rustc_type);
            self.attach_tag_to_elements(*tag, root_path.clone(), root_rustc_type);
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
                let old_layout = self.lookup_path_and_refine_result(
                    layout_path.clone(),
                    ExpressionType::NonPrimitive.as_rustc_type(self.tcx),
                );
                if let Expression::HeapBlockLayout { .. } = &old_layout.expression {
                    if self.check_for_errors {
                        self.check_for_layout_consistency(
                            &old_layout.expression,
                            new_layout_expression,
                        );
                    }
                    let mut purged_map = self.current_environment.value_map.clone();
                    for (path, _) in self
                        .current_environment
                        .value_map
                        .iter()
                        .filter(|(p, _)| (**p) == *qualifier || p.is_rooted_by(&qualifier))
                    {
                        purged_map = purged_map.remove(path);
                    }
                    self.current_environment.value_map = purged_map;
                }
            }
        } else {
            assume_unreachable!("Layout values should only be associated with layout paths");
        }
    }

    /// Following a reallocation we are no longer guaranteed that the resulting heap
    /// memory block has been zeroed out by the allocator. Search the environment for equivalent
    /// heap block values and update them to clear the zeroed flag (if set).
    #[logfn_inputs(TRACE)]
    fn update_zeroed_flag_for_heap_block_from_environment(
        &mut self,
        layout_path: &Rc<Path>,
        new_layout_expression: &Expression,
    ) {
        if let PathEnum::QualifiedPath { qualifier, .. } = &layout_path.value {
            if self.check_for_errors {
                let old_layout = self.lookup_path_and_refine_result(
                    layout_path.clone(),
                    ExpressionType::NonPrimitive.as_rustc_type(self.tcx),
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
                        let new_block = AbstractValue::make_from(
                            Expression::HeapBlock {
                                abstract_address: *abstract_address,
                                is_zeroed: false,
                            },
                            1,
                        );
                        let new_block_path = Path::get_as_path(new_block);
                        let mut updated_value_map = self.current_environment.value_map.clone();
                        for (path, value) in self.current_environment.value_map.iter() {
                            match &value.expression {
                                Expression::Reference(p) => {
                                    if *p == *qualifier || p.is_rooted_by(qualifier) {
                                        let new_block_path =
                                            p.replace_root(qualifier, new_block_path.clone());
                                        let new_reference =
                                            AbstractValue::make_reference(new_block_path);
                                        updated_value_map.insert_mut(path.clone(), new_reference);
                                    }
                                }
                                Expression::Variable { path: p, var_type } => {
                                    if *p == *qualifier || p.is_rooted_by(qualifier) {
                                        let new_block_path =
                                            p.replace_root(qualifier, new_block_path.clone());
                                        let new_variable = AbstractValue::make_typed_unknown(
                                            var_type.clone(),
                                            new_block_path,
                                        );
                                        updated_value_map.insert_mut(path.clone(), new_variable);
                                    }
                                }
                                _ => (),
                            }
                        }
                        self.current_environment.value_map = updated_value_map;
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
        precondition!(self.check_for_errors);
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
                let warning = self.cv.session.struct_span_warn(
                    self.current_span,
                    "the pointer points to memory that has already been deallocated",
                );
                self.emit_diagnostic(warning);
            }
            let layouts_match = old_length
                .equals(new_length.clone())
                .and(old_alignment.equals(new_alignment.clone()));
            let (layouts_match_as_bool, entry_cond_as_bool) =
                self.check_condition_value_and_reachability(&layouts_match);
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
                let warning = self
                    .cv
                    .session
                    .struct_span_warn(self.current_span, &message);
                self.emit_diagnostic(warning);
            }
        }
    }

    /// Checks the given condition value and also checks if the current entry condition can be true.
    /// If the abstract domains are undecided, resort to using the SMT solver.
    /// Only call this when doing actual error checking, since this is expensive.
    #[logfn_inputs(TRACE)]
    #[logfn(TRACE)]
    fn check_condition_value_and_reachability(
        &mut self,
        cond_val: &Rc<AbstractValue>,
    ) -> (Option<bool>, Option<bool>) {
        trace!(
            "entry condition {:?}",
            self.current_environment.entry_condition
        );
        // Check if the condition is always true (or false) if we get here.
        let mut cond_as_bool = cond_val.as_bool_if_known();
        // Check if we can prove that every call to the current function will reach this call site.
        let mut entry_cond_as_bool = self.current_environment.entry_condition.as_bool_if_known();
        // Use SMT solver if need be.
        if let Some(entry_cond_as_bool) = entry_cond_as_bool {
            if entry_cond_as_bool && cond_as_bool.is_none() {
                cond_as_bool = self.solve_condition(cond_val);
            }
        } else {
            // Check if path implies condition
            if cond_as_bool.unwrap_or(false)
                || self.current_environment.entry_condition.implies(cond_val)
            {
                return (Some(true), None);
            }
            if !cond_as_bool.unwrap_or(true)
                || self
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

    /// Copies/moves all paths rooted in source_path to corresponding paths rooted in target_path.
    /// source_path and/or target_path may be pattern paths and will be expanded as needed.
    #[allow(clippy::suspicious_else_formatting)]
    #[logfn_inputs(TRACE)]
    pub fn copy_or_move_elements(
        &mut self,
        target_path: Rc<Path>,
        source_path: Rc<Path>,
        root_rustc_type: Ty<'tcx>,
        move_elements: bool,
    ) {
        check_for_early_return!(self);
        // Some qualified source_paths are patterns that select one or more values from
        // a collection of values obtained from the qualifier. We need to copy/move those
        // individually, hence we use a helper to call copy_or_move_elements recursively on
        // each source_path expansion.
        let expanded_source_pattern = self.try_expand_source_pattern(
            &target_path,
            &source_path,
            root_rustc_type,
            |_self, target_path, expanded_path, ty| {
                _self.copy_or_move_elements(target_path, expanded_path, ty, move_elements)
            },
        );
        if expanded_source_pattern {
            return;
        }

        // Get here if source_path is not a pattern. Now see if target_path is a pattern.
        // First look for assignments to union fields. Those have become (strong) assignments to
        // every field of the union because union fields all alias the same underlying storage.
        if let PathEnum::QualifiedPath {
            qualifier,
            selector,
            ..
        } = &target_path.value
        {
            if let PathSelector::UnionField { num_cases, .. } = selector.as_ref() {
                for i in 0..*num_cases {
                    let target_path = Path::new_union_field(qualifier.clone(), i, *num_cases);
                    self.non_patterned_copy_or_move_elements(
                        target_path,
                        source_path.clone(),
                        root_rustc_type,
                        move_elements,
                        |_self, path, _, new_value| {
                            _self.current_environment.update_value_at(path, new_value);
                        },
                    );
                }
                return;
            }
        }

        // Now look for slice/index patterns.
        // If a slice pattern is a known size, copy_of_move_elements is called recursively
        // on each expansion of the target pattern and try_expand_target_pattern returns true.
        // If not, all of the paths that might match the pattern are weakly updated to account
        // for the possibility that this assignment might update them (or not).
        let expanded_target_pattern = self.try_expand_target_pattern(
            &target_path,
            &source_path,
            root_rustc_type,
            |_self, target_path, source_path, root_rustc_type| {
                _self.copy_or_move_elements(
                    target_path,
                    source_path,
                    root_rustc_type,
                    move_elements,
                );
            },
            |_self, target_path, source_path, index_value: Rc<AbstractValue>| {
                _self.weak_updates(&target_path, &source_path, |v| index_value.equals(v));
            },
            |_self, target_path, _source_path, count: Rc<AbstractValue>| {
                _self.weaken_paths_that_index(&target_path, &count);
            },
        );
        if expanded_target_pattern {
            // The assignment became a deterministic slice assignment and we are now done with it.
            return;
        }

        self.distribute_over_target_joins(
            target_path,
            Rc::new(abstract_value::TRUE),
            &|_self, sub_path| {
                _self.non_patterned_copy_or_move_elements(
                    sub_path,
                    source_path.clone(),
                    root_rustc_type,
                    move_elements,
                    |_self, path, _, new_value| {
                        _self.current_environment.update_value_at(path, new_value);
                    },
                );
            },
            &|_self, sub_path, condition| {
                _self.non_patterned_copy_or_move_elements(
                    sub_path,
                    source_path.clone(),
                    root_rustc_type,
                    move_elements,
                    |_self, path, old_value, new_value| {
                        let weak_value = condition.conditional_expression(new_value, old_value);
                        _self.current_environment.update_value_at(path, weak_value);
                    },
                )
            },
        );
    }

    /// If source_path is a qualified path with a path selector that is a pattern of some sort
    /// then expand the pattern into one more simpler paths and call F(target_path, simpler_path)
    /// on each simpler path.
    pub fn try_expand_source_pattern<F>(
        &mut self,
        target_path: &Rc<Path>,
        source_path: &Rc<Path>,
        root_rustc_ty: Ty<'tcx>,
        update: F,
    ) -> bool
    where
        F: Fn(&mut Self, Rc<Path>, Rc<Path>, Ty<'tcx>),
    {
        if let PathEnum::QualifiedPath {
            ref qualifier,
            ref selector,
            ..
        } = &source_path.value
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
                            // can't expand the pattern because the length is not known at this point
                            return false;
                        }
                    } else {
                        u128::from(offset)
                    };
                    let index_val = self.get_u128_const_val(index);
                    let index_path = Path::new_index(qualifier.clone(), index_val)
                        .refine_paths(&self.current_environment);
                    let elem_ty = type_visitor::get_element_type(root_rustc_ty);
                    update(self, target_path.clone(), index_path, elem_ty);
                    return true;
                }
                PathSelector::ConstantSlice { from, to, from_end } => {
                    let len_value = self.get_len(qualifier.clone());
                    if let AbstractValue {
                        expression: Expression::CompileTimeConstant(ConstantDomain::U128(len)),
                        ..
                    } = len_value.as_ref()
                    {
                        let to = if from_end {
                            u32::try_from(*len).unwrap() - to
                        } else {
                            to
                        };
                        self.expand_slice(target_path, qualifier, root_rustc_ty, from, to, update);
                        return true;
                    }
                }
                _ => (),
            }
        };
        false
    }

    /// Call F(target_path[i - from]), source_path[i]) for i in from..to
    /// For example, if F is a copy operation, this performs a slice copy.
    pub fn expand_slice<F>(
        &mut self,
        target_path: &Rc<Path>,
        source_path: &Rc<Path>,
        root_rustc_type: Ty<'tcx>,
        from: u32,
        to: u32,
        update: F,
    ) where
        F: Fn(&mut Self, Rc<Path>, Rc<Path>, Ty<'tcx>),
    {
        let mut elem_ty = type_visitor::get_element_type(root_rustc_type);
        if elem_ty == root_rustc_type {
            elem_ty = type_visitor::get_target_type(root_rustc_type);
        }
        let source_val = self.lookup_path_and_refine_result(source_path.clone(), elem_ty);
        if matches!(source_val.expression, Expression::CompileTimeConstant(..)) {
            let source_path = Path::new_alias(source_val);
            for i in from..to {
                let target_index_val = self.get_u128_const_val(u128::try_from(i - from).unwrap());
                let indexed_target = Path::new_index(target_path.clone(), target_index_val)
                    .refine_paths(&self.current_environment);
                update(self, indexed_target, source_path.clone(), elem_ty);
            }
        } else {
            //todo: if the target slice overlaps with the source_slice the logic below will do the wrong
            //thing. Fix this by introducing some kind of temporary storage.
            for i in from..to {
                let index_val = self.get_u128_const_val(u128::from(i));
                let indexed_source = Path::new_index(source_path.clone(), index_val)
                    .refine_paths(&self.current_environment);
                let target_index_val = self.get_u128_const_val(u128::try_from(i - from).unwrap());
                let indexed_target = Path::new_index(target_path.clone(), target_index_val)
                    .refine_paths(&self.current_environment);
                trace!(
                    "indexed_target {:?} indexed_source {:?} elem_ty {:?}",
                    indexed_target,
                    indexed_source,
                    elem_ty
                );
                update(self, indexed_target, indexed_source, elem_ty);
            }
        }
    }

    /// If target_path is a slice of known size, this amounts to a series of assignments
    /// to each, known, slice element. In this case the function returns true.
    /// If target_path is a "pattern" that may match one or more other paths in the environment,
    /// depending on some unknown value, then these other paths are "weakly" updated to reflect
    /// the possibility that this assignment might modify the values that are currently associated
    /// with them. In this case the function returns false so that the caller can proceed to
    /// also, strongly, update the target_path without treating it as a pattern.
    pub fn try_expand_target_pattern<F, G, H>(
        &mut self,
        target_path: &Rc<Path>,
        source_path: &Rc<Path>,
        root_rustc_type: Ty<'tcx>,
        strong_update: F,
        weak_update: G,
        weak_update_slice: H,
    ) -> bool
    where
        F: Fn(&mut Self, Rc<Path>, Rc<Path>, Ty<'tcx>),
        G: Fn(&mut Self, Rc<Path>, Rc<Path>, Rc<AbstractValue>),
        H: Fn(&mut Self, Rc<Path>, Rc<Path>, Rc<AbstractValue>),
    {
        if let PathEnum::QualifiedPath {
            ref qualifier,
            ref selector,
            ..
        } = &target_path.value
        {
            match &**selector {
                PathSelector::Index(value) => {
                    if let Expression::CompileTimeConstant(..) = &value.expression {
                        // fall through, the target path is unique
                    } else {
                        weak_update(self, qualifier.clone(), source_path.clone(), value.clone());
                        // fall through
                    }
                }
                PathSelector::Slice(count) => {
                    // if the count is known at this point, expand it like a pattern.
                    if let Expression::CompileTimeConstant(ConstantDomain::U128(val)) =
                        &count.expression
                    {
                        self.expand_slice(
                            qualifier,
                            source_path,
                            root_rustc_type,
                            0,
                            *val as u32,
                            strong_update,
                        );
                        return true;
                    } else {
                        // Any element that that might get assigned to via this slice need to get weakened.
                        // That is, the value has to become a condition based on index < count.
                        weak_update_slice(
                            self,
                            qualifier.clone(),
                            source_path.clone(),
                            count.clone(),
                        )
                        // fall through
                    }
                }
                _ => {
                    // fall through
                }
            }
        }

        // Assigning to a fixed length array is like a pattern
        if let TyKind::Array(_, len) = &root_rustc_type.kind {
            let param_env = self.type_visitor.get_param_env();
            let len = len
                .try_eval_usize(self.tcx, param_env)
                .expect("Array to have constant len");

            self.expand_slice(
                target_path,
                source_path,
                root_rustc_type,
                0,
                len as u32,
                strong_update,
            );
            return true;
        }
        false
    }

    /// If the target path if of the form if c { p1 } else { p2 } then it is an alias for either
    /// p1 or p2, so updating the target path must weakly update p1 and p2 as well.
    pub fn distribute_over_target_joins<F, G>(
        &mut self,
        target_path: Rc<Path>,
        join_prefix: Rc<AbstractValue>,
        strong_update: &F,
        weak_update: &G,
    ) where
        F: Fn(&mut Self, Rc<Path>),
        G: Fn(&mut Self, Rc<Path>, Rc<AbstractValue>),
    {
        trace!(
            "target_path {:?} join_prefix {:?}",
            target_path,
            join_prefix
        );
        if let Some((join_condition, true_path, false_path)) =
            self.current_environment.try_to_split(&target_path)
        {
            if join_prefix.as_bool_if_known().unwrap_or(false) {
                //todo: if the strong update is a move, the weak updates below do not see the values
                //rooted at the source path because they have moved. On the other hand, if the strong
                //update is done after the weak updates, then the strong update can't help to refine
                //the weak values.
                // For now we work around this problem by always copying.
                strong_update(self, target_path);
            }
            // The value path contains an abstract value that was constructed with a join.
            // In this case, we split the path into two and perform weak updates on them.
            // Rather than do it here, we recurse until there are no more joins.
            self.distribute_over_target_joins(
                true_path,
                join_prefix.and(join_condition.clone()),
                strong_update,
                weak_update,
            );
            self.distribute_over_target_joins(
                false_path,
                join_prefix.and(join_condition.logical_not()),
                strong_update,
                weak_update,
            );
        } else {
            // Get here for a path with no joins.
            if join_prefix.as_bool_if_known().unwrap_or(false) {
                // This is the root call, so just do a strong update and return to the caller.
                strong_update(self, target_path)
            } else {
                // This is a recursive call, do the weak update and return to the caller.
                // The caller will do the strong update if it is the root call.
                weak_update(self, target_path, join_prefix);
            }
        }
    }

    /// Copies/moves all paths rooted in source_path to corresponding paths rooted in target_path.
    pub fn non_patterned_copy_or_move_elements<F>(
        &mut self,
        target_path: Rc<Path>,
        source_path: Rc<Path>,
        root_rustc_type: Ty<'tcx>,
        move_elements: bool,
        update: F,
    ) where
        F: Fn(&mut Self, Rc<Path>, Rc<AbstractValue>, Rc<AbstractValue>),
    {
        trace!("non_patterned_copy_or_move_elements(target_path {:?}, source_path {:?}, root_rustc_type {:?})", target_path, source_path, root_rustc_type);
        let value = self.lookup_path_and_refine_result(source_path.clone(), root_rustc_type);
        let val_type = value.expression.infer_type();
        let mut no_children = true;
        // If a non primitive parameter is just returned from a function, for example,
        // there will be no entries rooted with target_path in the final environment.
        // This will lead to an incorrect summary of the function, since only the paths
        // in the final environment are used construct the summary. We work around this
        // by creating an entry for the non primitive (unknown) value. The caller will
        // be saddled with removing it. This case corresponds to no_children being true.
        if val_type == ExpressionType::NonPrimitive {
            // First look at paths that are rooted in rpath.
            // Remove an explicit deref from source_path to make it a valid root.
            let source_path = match &source_path.value {
                PathEnum::QualifiedPath {
                    qualifier,
                    selector,
                    ..
                } if **selector == PathSelector::Deref => qualifier.clone(),
                _ => source_path,
            };
            let value_map = self.current_environment.value_map.clone();
            for (path, value) in value_map
                .iter()
                .filter(|(p, _)| p.is_rooted_by(&source_path))
            {
                check_for_early_return!(self);
                let qualified_path = path
                    .replace_root(&source_path, target_path.clone())
                    .refine_paths(&self.current_environment);
                if move_elements {
                    trace!("moving child {:?} to {:?}", value, qualified_path);
                // todo: doing the remove part of the move here makes it difficult to combine
                // strong updates with weak updates. See comments in distribute_over_target_joins.
                // self.current_environment.value_map =
                //     self.current_environment.value_map.remove(path);
                } else {
                    trace!("copying child {:?} to {:?}", value, qualified_path);
                };
                let old_value = value_map.get(&qualified_path).unwrap_or(&value);
                update(self, qualified_path, old_value.clone(), value.clone());
                no_children = false;
            }
            if let Expression::RefinedParameterCopy { path, .. }
            | Expression::Variable { path, .. } = &value.expression
            {
                if path.is_rooted_by_parameter() {
                    update(self, target_path.clone(), value.clone(), value.clone());
                    no_children = false;
                }
            }
        }
        let target_type: ExpressionType = (&root_rustc_type.kind).into();
        if target_type != ExpressionType::NonPrimitive
            || no_children
            || root_rustc_type.is_closure()
        {
            let old_value =
                self.lookup_path_and_refine_result(target_path.clone(), root_rustc_type);
            // Just copy/move (rpath, value) itself.
            if move_elements {
                trace!("moving {:?} to {:?}", value, target_path);
            // todo: doing the remove part of the move here makes it difficult to combine
            // strong updates with weak updates. See comments in distribute_over_target_joins.
            // self.current_environment.value_map =
            //     self.current_environment.value_map.remove(&source_path);
            } else {
                trace!("copying {:?} to {:?}", value, target_path);
            }
            if let Expression::CompileTimeConstant(ConstantDomain::Str(s)) = &value.expression {
                // The value is a string literal. See if the target will treat it as &[u8].
                if let TyKind::Ref(_, ty, _) = root_rustc_type.kind {
                    if let TyKind::Slice(elem_ty) = ty.kind {
                        if let TyKind::Uint(rustc_ast::ast::UintTy::U8) = elem_ty.kind {
                            self.expand_aliased_string_literals_if_appropriate(
                                &target_path,
                                &value,
                                s,
                                update,
                            );
                            return;
                        }
                    }
                }
            }
            update(self, target_path, old_value, value);
        }
    }

    /// Weaken (path, value) pairs from the environment if path is rooted by root_path[index].
    /// Do so by replacing value with: if index < count { unknown_var } else { value }
    #[logfn_inputs(TRACE)]
    fn weaken_paths_that_index(&mut self, root_path: &Rc<Path>, count: &Rc<AbstractValue>) {
        let mut value_map = self.current_environment.value_map.clone();
        for (path, value) in self.current_environment.value_map.iter() {
            if let Some(index) = path.get_index_value_qualified_by(root_path) {
                //todo: can we do better than this?
                let unknown_value =
                    AbstractValue::make_typed_unknown(value.expression.infer_type(), path.clone());
                let weakened_value = index
                    .less_than(count.clone())
                    .conditional_expression(unknown_value.clone(), value.clone());
                value_map.insert_mut(path.clone(), weakened_value);
            }
        }
        self.current_environment.value_map = value_map;
    }

    /// Update all index entries rooted at target_path_root to reflect the possibility
    /// that an assignment via an unknown index value might change their current value.
    fn weak_updates<F>(
        &mut self,
        target_path_root: &Rc<Path>,
        source_path: &Rc<Path>,
        make_condition: F,
    ) where
        F: Fn(Rc<AbstractValue>) -> Rc<AbstractValue>,
    {
        let old_value_map = self.current_environment.value_map.clone();
        let mut new_value_map = old_value_map.clone();
        for (path, value) in old_value_map
            .iter()
            .filter(|(path, _)| path.is_rooted_by(target_path_root))
        {
            // See if path is of the form target_root_path[index_value].some_or_no_selectors
            let mut subsequent_selectors: Vec<Rc<PathSelector>> = Vec::new();
            if let Some(index_value) = self.extract_index_and_subsequent_selectors(
                path,
                target_path_root,
                &mut subsequent_selectors,
            ) {
                // If the join condition is true, the value at path needs updating.
                let join_condition = make_condition(index_value.clone());

                // Look up value at source_path_with_selectors.
                // source_path_with_selectors is of the form source_path.some_or_no_selectors.
                // This is the value to bind to path if the join condition is true.
                let source_path_with_selectors =
                    Path::add_selectors(source_path, &subsequent_selectors);
                let result_type = value.expression.infer_type();
                let result_rustc_type = result_type.as_rustc_type(self.tcx);
                let additional_value = self
                    .lookup_path_and_refine_result(source_path_with_selectors, result_rustc_type);
                let updated_value =
                    join_condition.conditional_expression(additional_value, value.clone());

                new_value_map.insert_mut(path.clone(), updated_value);
            }
        }
        self.current_environment.value_map = new_value_map;
    }

    /// If the given path is of the form root[index_value].selector1.selector2... then
    /// return the index_value and appends [selector1, selector2, ..] to selectors.
    /// Returns None otherwise. Does not append anything if [index_value] is the last selector.
    #[logfn_inputs(TRACE)]
    fn extract_index_and_subsequent_selectors(
        &self,
        path: &Rc<Path>,
        root: &Rc<Path>,
        selectors: &mut Vec<Rc<PathSelector>>,
    ) -> Option<Rc<AbstractValue>> {
        if let PathEnum::QualifiedPath {
            qualifier,
            selector,
            ..
        } = &path.value
        {
            if qualifier.eq(&root) {
                if let PathSelector::Index(index_value) = &**selector {
                    return Some(index_value.clone());
                }
            } else {
                let index_value =
                    self.extract_index_and_subsequent_selectors(qualifier, root, selectors);
                selectors.push(selector.clone());
                return index_value;
            }
        }
        None
    }

    // Most of the time, references to string values are just moved around from one memory location
    // to another and sometimes their lengths are taken. For such things there is no need to track
    // the value of each character as a separate (path, char) tuple in the environment. That just
    // slows things down and makes debugging more of chore.
    // As soon as a string value manages to flow into a variable of type &[u8], however, we can
    // expect expressions that look up individual characters and so we must enhance the current
    // environment with (path, char) tuples. The root of the path part of such a tuple is the
    // string literal itself, not the variable, which holds a pointer to the string.
    pub fn expand_aliased_string_literals_if_appropriate<F>(
        &mut self,
        target_path: &Rc<Path>,
        value: &Rc<AbstractValue>,
        str_val: &str,
        update: F,
    ) where
        F: Fn(&mut Self, Rc<Path>, Rc<AbstractValue>, Rc<AbstractValue>),
    {
        let collection_path = Path::new_alias(value.clone());
        // Create index elements
        for (i, ch) in str_val.as_bytes().iter().enumerate() {
            let index = Rc::new((i as u128).into());
            let ch_const: Rc<AbstractValue> = Rc::new((*ch as u128).into());
            let path = Path::new_index(collection_path.clone(), index);
            update(self, path, ch_const.clone(), ch_const);
        }
        // Arrays have a length field
        let length_val: Rc<AbstractValue> = Rc::new((str_val.len() as u128).into());
        let str_length_path = Path::new_length(collection_path);
        update(
            self,
            str_length_path,
            length_val.clone(),
            length_val.clone(),
        );
        // The target path is a fat pointer, initialize it.
        let thin_pointer_path = Path::new_field(target_path.clone(), 0);
        let thin_pointer_to_str = AbstractValue::make_reference(Path::get_as_path(value.clone()));
        update(
            self,
            thin_pointer_path,
            thin_pointer_to_str.clone(),
            thin_pointer_to_str,
        );
        let slice_length_path = Path::new_length(target_path.clone());
        update(self, slice_length_path, length_val.clone(), length_val);
    }

    /// Get the length of an array. Will be a compile time constant if the array length is known.
    #[logfn_inputs(TRACE)]
    fn get_len(&mut self, path: Rc<Path>) -> Rc<AbstractValue> {
        let length_path = Path::new_length(path).refine_paths(&self.current_environment);
        self.lookup_path_and_refine_result(length_path, self.tcx.types.usize)
    }

    /// Allocates a new heap block and caches it, keyed with the current location
    /// so that subsequent visits deterministically use the same heap block when processing
    /// the instruction at this location. If we don't do this the fixed point loop wont converge.
    /// Note, however, that this is not good enough for the outer fixed point because the counter
    /// is shared between different functions unless it is reset to 0 for each function.
    #[logfn_inputs(TRACE)]
    pub fn get_new_heap_block(
        &mut self,
        length: Rc<AbstractValue>,
        alignment: Rc<AbstractValue>,
        is_zeroed: bool,
        ty: Ty<'tcx>,
    ) -> Rc<AbstractValue> {
        let addresses = &mut self.heap_addresses;
        let constants = &mut self.cv.constant_value_cache;
        let block = addresses
            .entry(self.current_location)
            .or_insert_with(|| AbstractValue::make_from(constants.get_new_heap_block(is_zeroed), 1))
            .clone();
        let block_path = Path::get_as_path(block.clone());
        self.type_visitor
            .path_ty_cache
            .insert(block_path.clone(), ty);
        let layout_path = Path::new_layout(block_path);
        let layout = AbstractValue::make_from(
            Expression::HeapBlockLayout {
                length,
                alignment,
                source: LayoutSource::Alloc,
            },
            1,
        );
        self.current_environment
            .update_value_at(layout_path, layout);
        block
    }

    /// Attach `tag` to the value located at `value_path`. The `value_path` may be pattern paths
    /// and need be expanded.
    #[allow(clippy::suspicious_else_formatting)]
    #[logfn_inputs(TRACE)]
    pub fn attach_tag_to_elements(
        &mut self,
        tag: Tag,
        value_path: Rc<Path>,
        root_rustc_type: Ty<'tcx>,
    ) {
        // The value path contains an index/slice selector, e.g., arr[i]. If the index pattern is
        // concrete, e.g. the index i is a constant, we need to expand it and then use a helper
        // function to call attach_tag_to_elements recursively on each expansion.
        let expanded_source_pattern = self.try_expand_source_pattern(
            &value_path,
            &value_path,
            root_rustc_type,
            |_self, _target_path, expanded_path, root_rustc_type| {
                _self.attach_tag_to_elements(tag, expanded_path, root_rustc_type);
            },
        );
        if expanded_source_pattern {
            return;
        }

        // Get here if value_path is not a source pattern.
        // Now see if value_path is a target pattern.
        // First look for union fields. We have to attach the tag to every field of the union
        // because union fields all alias the same underlying storage.
        if let PathEnum::QualifiedPath {
            qualifier,
            selector,
            ..
        } = &value_path.value
        {
            if let PathSelector::UnionField { num_cases, .. } = selector.as_ref() {
                for i in 0..*num_cases {
                    let value_path = Path::new_union_field(qualifier.clone(), i, *num_cases);
                    self.non_patterned_copy_or_move_elements(
                        value_path.clone(),
                        value_path,
                        root_rustc_type,
                        false,
                        |_self, path, _, new_value| {
                            _self
                                .current_environment
                                .value_map
                                .insert_mut(path, new_value.add_tag(tag));
                        },
                    );
                }
                return;
            }
        }

        // Get here if value path is not a pattern, or it contains an abstract index/slice selector.
        // Consider the case where the value path contains an abstract index/slice selector.
        // If the index/slice selector is a compile-time constant, then we use a helper function
        // to call attach_tag_to_elements recursively on each expansion.
        // If not, all the paths that can match the pattern are weakly attached with the tag.
        let expanded_target_pattern = self.try_expand_target_pattern(
            &value_path,
            &value_path,
            root_rustc_type,
            |_self, _target_path, expanded_path, root_rustc_type| {
                _self.attach_tag_to_elements(tag, expanded_path, root_rustc_type);
            },
            |_self, target_path, _source_path, index_value| {
                _self.attach_tag_weakly(tag, &target_path, |v| index_value.equals(v));
            },
            |_self, target_path, _source_path, count| {
                _self.attach_tag_weakly(tag, &target_path, |v| count.greater_than(v));
            },
        );
        if expanded_target_pattern {
            return;
        }

        self.distribute_over_target_joins(
            value_path,
            Rc::new(abstract_value::TRUE),
            &|_self, sub_path| {
                if !root_rustc_type.is_scalar() {
                    let (tag_field_path, tag_field_value) =
                        _self.extract_tag_field_of_non_scalar_value_at(&sub_path, root_rustc_type);
                    _self
                        .current_environment
                        .value_map
                        .insert_mut(tag_field_path, tag_field_value.add_tag(tag));
                    if !tag.is_propagated_by(TagPropagation::SubComponent) {
                        return;
                    } else {
                        // fall through, the tag is propagated to sub-components.
                    }
                }

                // We gets here if root_rustc_type is scalar or the tag can be propagated to sub-components.
                _self.non_patterned_copy_or_move_elements(
                    sub_path.clone(),
                    sub_path.clone(),
                    root_rustc_type,
                    false,
                    |_self, path, _, new_value| {
                        // Layout and Discriminant are not accessible to programmers, and they carry internal information
                        // that should not be wrapped by tags. TagField is also skipped, because they will be handled
                        // together with implicit tag fields.
                        if let PathEnum::QualifiedPath { selector, .. } = &path.value {
                            if matches!(
                                **selector,
                                PathSelector::Layout
                                    | PathSelector::Discriminant
                                    | PathSelector::TagField
                            ) {
                                return;
                            }
                        }

                        // We should update the tag fields of non-scalar values.
                        // The logic is implemented in propagate_tag_to_tag_fields.
                        let path_rustc_type = _self
                            .type_visitor
                            .get_path_rustc_type(&path, _self.current_span);
                        if !path_rustc_type.is_scalar() {
                            return;
                        }

                        _self
                            .current_environment
                            .value_map
                            .insert_mut(path, new_value.add_tag(tag));
                    },
                );

                // Propagate the tag to all tag fields rooted by sub_path.
                _self.propagate_tag_to_tag_fields(sub_path, |value| value.add_tag(tag));
            },
            &|_self, sub_path, condition| {
                if !root_rustc_type.is_scalar() {
                    let (tag_field_path, tag_field_value) =
                        _self.extract_tag_field_of_non_scalar_value_at(&sub_path, root_rustc_type);
                    let weak_value = condition
                        .conditional_expression(tag_field_value.add_tag(tag), tag_field_value);
                    _self
                        .current_environment
                        .value_map
                        .insert_mut(tag_field_path, weak_value);
                    if !tag.is_propagated_by(TagPropagation::SubComponent) {
                        return;
                    } else {
                        // fall through, the tag is propagated to sub-components.
                    }
                }

                // We gets here if root_rustc_type is scalar or the tag can be propagated to sub-components.
                _self.non_patterned_copy_or_move_elements(
                    sub_path.clone(),
                    sub_path.clone(),
                    root_rustc_type,
                    false,
                    |_self, path, old_value, new_value| {
                        // Layout and Discriminant are not accessible to programmers, and they carry internal information
                        // that should not be wrapped by tags. TagField is also skipped, because they will be handled
                        // together with implicit tag fields.
                        if let PathEnum::QualifiedPath { selector, .. } = &path.value {
                            if matches!(
                                **selector,
                                PathSelector::Layout
                                    | PathSelector::Discriminant
                                    | PathSelector::TagField
                            ) {
                                return;
                            }
                        }

                        // We should update the tag fields of non-scalar values.
                        // The logic is implemented in propagate_tag_to_tag_fields.
                        let path_rustc_type = _self
                            .type_visitor
                            .get_path_rustc_type(&path, _self.current_span);
                        if !path_rustc_type.is_scalar() {
                            return;
                        }

                        let weak_value =
                            condition.conditional_expression(new_value.add_tag(tag), old_value);
                        _self
                            .current_environment
                            .value_map
                            .insert_mut(path, weak_value);
                    },
                );

                // Propagate the tag to all tag fields rooted by sub_path.
                _self.propagate_tag_to_tag_fields(sub_path, |value| {
                    condition.conditional_expression(value.add_tag(tag), value)
                });
            },
        );
    }

    /// Attach `tag` to all index entries rooted at qualifier to reflect the possibility
    /// that tagging an entry at an unknown index might also tag them.
    fn attach_tag_weakly<F>(&mut self, tag: Tag, qualifier: &Rc<Path>, make_condition: F)
    where
        F: Fn(Rc<AbstractValue>) -> Rc<AbstractValue>,
    {
        let value_map = self.current_environment.value_map.clone();
        for (path, old_value) in value_map.iter().filter(|(p, _)| p.is_rooted_by(qualifier)) {
            let mut subsequent_selectors = Vec::new();
            if let Some(index_value) = self.extract_index_and_subsequent_selectors(
                path,
                qualifier,
                &mut subsequent_selectors,
            ) {
                let join_condition = make_condition(index_value.clone());
                let new_value = join_condition
                    .conditional_expression(old_value.add_tag(tag), old_value.clone());
                self.current_environment
                    .value_map
                    .insert_mut(path.clone(), new_value);
            }
        }
    }

    /// Extract the path and the value of the tag field of the value located at `qualifier`.
    /// If the tag field is not tracked in the current environment, then either return an
    /// unknown value (if `qualifier` is rooted at a parameter), or return a dummy untagged
    /// value (if `qualifier` is rooted at a local variable).
    #[logfn_inputs(TRACE)]
    #[logfn(TRACE)]
    pub fn extract_tag_field_of_non_scalar_value_at(
        &mut self,
        qualifier: &Rc<Path>,
        root_rustc_type: Ty<'tcx>,
    ) -> (Rc<Path>, Rc<AbstractValue>) {
        precondition!(!root_rustc_type.is_scalar());

        let tag_field_path =
            Path::new_tag_field(qualifier.clone()).refine_paths(&self.current_environment);
        let mut tag_field_value = self.lookup_path_and_refine_result(
            tag_field_path.clone(),
            self.type_visitor.dummy_untagged_value_type,
        );

        // Consider the case where there is no value for the tag field in the environment, i.e.,
        // the result of the lookup is just a variable that reflects tag_field_path.
        if matches!(&tag_field_value.expression, Expression::RefinedParameterCopy {path, ..} | Expression::Variable { path, .. } if path.eq(&tag_field_path))
        {
            if qualifier.is_rooted_by_parameter() {
                // If qualifier is rooted by a function parameter, return an unknown tag field.
                tag_field_value = AbstractValue::make_from(
                    Expression::UnknownTagField {
                        path: tag_field_path.clone(),
                    },
                    1,
                );
            } else {
                // Otherwise, return a dummy untagged value.
                tag_field_value = Rc::new(abstract_value::DUMMY_UNTAGGED_VALUE);
            }

            self.current_environment
                .value_map
                .insert_mut(tag_field_path.clone(), tag_field_value.clone());
        }

        (tag_field_path, tag_field_value)
    }

    /// Attach a tag to all tag field paths that are rooted by root_path.
    /// If v is the value at a tag field path, then it is updated to attach_tag(v).
    fn propagate_tag_to_tag_fields<F>(&mut self, root_path: Rc<Path>, attach_tag: F)
    where
        F: Fn(Rc<AbstractValue>) -> Rc<AbstractValue>,
    {
        // Record visited prefixes of paths. We need this information to avoid handling the same prefix for multiple times.
        let mut visited_path_prefixes: HashSet<Rc<Path>> = HashSet::new();

        let old_value_map = self.current_environment.value_map.clone();

        for (path, _) in old_value_map
            .iter()
            .filter(|(p, _)| p.is_rooted_by(&root_path))
        {
            let mut path_prefix = path;

            loop {
                // If path_prefix has been visited, we exit the loop.
                if !visited_path_prefixes.insert(path_prefix.clone()) {
                    break;
                }

                // We get here if path_prefix is rooted by root_path and is not yet visited.
                let path_prefix_rustc_type = self
                    .type_visitor
                    .get_path_rustc_type(path_prefix, self.current_span);
                if !path_prefix_rustc_type.is_scalar() {
                    let (tag_field_path, tag_field_value) = self
                        .extract_tag_field_of_non_scalar_value_at(
                            path_prefix,
                            path_prefix_rustc_type,
                        );
                    self.current_environment
                        .value_map
                        .insert_mut(tag_field_path.clone(), attach_tag(tag_field_value));
                }

                if let PathEnum::QualifiedPath { qualifier, .. } = &path_prefix.value {
                    // If the qualifier is already root_path, i.e., none of the prefixes can be rooted by root_path,
                    // we exit the loop.
                    if *qualifier == root_path {
                        break;
                    } else {
                        path_prefix = qualifier;
                    }
                } else {
                    // If path_prefix is no longer a qualified path, we exit the loop.
                    break;
                }
            }
        }
    }
}
