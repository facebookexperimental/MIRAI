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
use crate::type_visitor::TypeVisitor;
use crate::{abstract_value, type_visitor};

use crate::block_visitor::BlockVisitor;
use crate::call_visitor::CallVisitor;
use crate::crate_visitor::CrateVisitor;
use crate::fixed_point_visitor::FixedPointVisitor;
use log_derive::*;
use mirai_annotations::*;
use rpds::HashTrieMap;
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
    pub mir: mir::ReadOnlyBodyAndCache<'analysis, 'tcx>,
    pub smt_solver: &'analysis mut dyn SmtSolver<E>,
    pub buffered_diagnostics: &'analysis mut Vec<DiagnosticBuilder<'compilation>>,
    pub active_calls_map: &'analysis mut HashMap<DefId, u64>,

    pub already_reported_errors_for_call_to: HashSet<Rc<AbstractValue>>,
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
    pub type_visitor: TypeVisitor<'analysis, 'tcx>,
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
        let mir = crate_visitor.tcx.optimized_mir(def_id).unwrap_read_only();
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

        // The entry block has no predecessors and its initial state is the function parameters
        // (which we omit here so that we can lazily provision them with additional context)
        // as well any promoted constants.
        let mut first_state = self.promote_constants();

        // Add parameter values that are function constants.
        for (path, val) in function_constant_args.iter() {
            TypeVisitor::add_function_constants_reachable_from(
                &mut self.current_environment,
                parameter_types,
                &mut first_state,
                &path,
            );
            first_state.value_map = first_state.value_map.insert(path.clone(), val.clone());
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

        if !fixed_point_visitor.bv.assume_function_is_angelic {
            // Now traverse the blocks again, doing checks and emitting diagnostics.
            // terminator_state[bb] is now complete for every basic block bb in the body.
            fixed_point_visitor.bv.check_for_errors(
                &fixed_point_visitor.block_indices,
                &mut fixed_point_visitor.terminator_state,
            );
            *self
                .active_calls_map
                .entry(self.def_id)
                .or_insert_with(|| unreachable!()) -= 1;
            let elapsed_time_in_seconds = self.start_instant.elapsed().as_secs();
            if elapsed_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
                self.report_timeout(elapsed_time_in_seconds);
            } else {
                // Now create a summary of the body that can be in-lined into call sites.
                if self.async_fn_summary.is_some() {
                    self.preconditions = self.translate_async_preconditions();
                    // todo: also translate side-effects, return result and post-condition
                };

                return summaries::summarize(
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
        let mut result = Summary::default();
        result.is_computed = true; // Otherwise this function keeps getting re-analyzed
        result.is_angelic = true; // Callers have to make possibly false assumptions.
        result
    }

    fn report_timeout(&mut self, elapsed_time_in_seconds: u64) {
        // This body is beyond MIRAI for now
        if self.cv.options.diag_level != DiagLevel::RELAXED {
            let error = self
                .cv
                .session
                .struct_span_err(self.current_span, "The analysis of this function timed out");
            self.emit_diagnostic(error);
        }
        warn!(
            "analysis of {} timed out after {} seconds",
            self.function_name, elapsed_time_in_seconds,
        );
        *self
            .active_calls_map
            .entry(self.def_id)
            .or_insert_with(|| unreachable!()) -= 1;
        self.assume_function_is_angelic = true;
    }

    /// Adds the given diagnostic builder to the buffer.
    /// Buffering diagnostics gives us the chance to sort them before printing them out,
    /// which is desirable for tools that compare the diagnostics from one run of MIRAI with another.
    #[logfn_inputs(TRACE)]
    pub fn emit_diagnostic(&mut self, mut diagnostic_builder: DiagnosticBuilder<'compilation>) {
        precondition!(self.check_for_errors);
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
            PathEnum::Alias { value } => {
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
        let result = if refined_val.is_bottom() {
            // Not found locally, so try statics.
            if let PathEnum::StaticVariable {
                def_id,
                ref summary_cache_key,
                ref expression_type,
            } = &path.value
            {
                self.lookup_static(&path, *def_id, summary_cache_key, expression_type)
            } else if path.path_length() < k_limits::MAX_PATH_LENGTH {
                let mut result = TypeVisitor::try_lookup_fat_pointer_ptr(
                    &self.current_environment,
                    &path,
                    &result_rustc_type,
                );
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
                    let result = if let PathEnum::LocalVariable { .. } = path.value {
                        refined_val
                    } else {
                        AbstractValue::make_typed_unknown(result_type.clone(), path.clone())
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
                    AbstractValue::make_typed_unknown(result_type.clone(), path.clone())
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
        if result_type != ExpressionType::Reference
            && result.expression.infer_type() == ExpressionType::Reference
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

    /// Gets the value of the given static variable by obtaining a summary for the corresponding def_id.
    #[logfn_inputs(TRACE)]
    fn lookup_static(
        &mut self,
        path: &Rc<Path>,
        def_id: Option<DefId>,
        summary_cache_key: &Rc<String>,
        expression_type: &ExpressionType,
    ) -> Rc<AbstractValue> {
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
        let side_effects = summary.side_effects.clone();
        // Effects on the path
        self.transfer_and_refine(&side_effects, path.clone(), &Path::new_result(), &[]);
        // Effects on the heap
        for (path, value) in side_effects.iter() {
            if path.is_rooted_by_abstract_heap_block() {
                self.current_environment
                    .update_value_at(path.clone(), value.clone());
            }
        }
        self.current_environment
            .value_at(&path)
            .cloned()
            .unwrap_or_else(|| {
                AbstractValue::make_typed_unknown(expression_type.clone(), path.clone())
            })
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
        let closure_object = self.get_new_heap_block(zero.clone(), zero, false);
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
            let value = self.lookup_path_and_refine_result(path, loc.ty);
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
                    .refine_parameters(&actual_args, self.fresh_variable_offset)
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
        let result_root: Rc<Path> = Path::new_result();
        for (ordinal, constant_mir) in self.tcx.promoted_mir(self.def_id).iter().enumerate() {
            self.mir = constant_mir.unwrap_read_only();
            self.type_visitor.mir = self.mir;
            let result_rustc_type = self.mir.local_decls[mir::Local::from(0usize)].ty;
            self.visit_promoted_constants_block();
            if self.exit_environment.is_some() {
                let promoted_root: Rc<Path> =
                    Rc::new(PathEnum::PromotedConstant { ordinal }.into());
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
                        // local_path is reference to a local of the promoted constant function so we
                        // need to rename the local so that it does not clash with the parent function's
                        // locals.
                        let new_local: Rc<Path> = Rc::new(
                            PathEnum::PromotedConstant {
                                ordinal: ordinal + 1000,
                            }
                            .into(),
                        );
                        for (path, value) in self
                            .exit_environment
                            .as_ref()
                            .unwrap()
                            .value_map
                            .iter()
                            .filter(|(p, _)| (*p) == local_path || p.is_rooted_by(local_path))
                        {
                            let renamed_path = path.replace_root(local_path, new_local.clone());
                            environment.update_value_at(renamed_path, value.clone());
                        }
                        let new_value = AbstractValue::make_reference(new_local);
                        environment.update_value_at(promoted_root.clone(), new_value);
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
    fn check_offset(&mut self, offset: &AbstractValue) {
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
    #[logfn_inputs(TRACE)]
    pub fn transfer_and_refine(
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
            trace!("effect {:?} {:?}", path, value);
            let dummy_root = Path::new_local(999);
            let refined_dummy_root = Path::new_local(self.fresh_variable_offset + 999);
            let tpath = path
                .replace_root(source_path, dummy_root)
                .refine_parameters(arguments, self.fresh_variable_offset)
                .replace_root(&refined_dummy_root, target_path.clone())
                .refine_paths(&self.current_environment);
            let rvalue = value
                .refine_parameters(arguments, self.fresh_variable_offset)
                .refine_paths(&self.current_environment);
            trace!("refined effect {:?} {:?}", tpath, rvalue);
            let rtype = rvalue.expression.infer_type();
            match &rvalue.expression {
                Expression::HeapBlock { .. } => {
                    if let PathEnum::QualifiedPath { selector, .. } = &tpath.value {
                        if let PathSelector::Slice(..) = selector.as_ref() {
                            let source_path = Path::get_as_path(rvalue.clone());
                            let target_type = type_visitor::get_element_type(
                                self.type_visitor
                                    .get_path_rustc_type(&target_path, self.current_span),
                            );
                            self.copy_or_move_elements(
                                tpath.clone(),
                                source_path,
                                target_type,
                                false,
                            );
                            continue;
                        }
                    }
                    self.current_environment.update_value_at(tpath, rvalue);
                    continue;
                }
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
                                    .refine_parameters(arguments, self.fresh_variable_offset)
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
                Expression::Offset { .. } => {
                    if self.check_for_errors && self.function_being_analyzed_is_root() {
                        self.check_offset(&rvalue);
                    }
                }
                Expression::UninterpretedCall {
                    callee,
                    arguments,
                    result_type,
                    ..
                } => {
                    let rvalue = callee.uninterpreted_call(
                        arguments.clone(),
                        result_type.clone(),
                        tpath.clone(),
                    );
                    self.current_environment.update_value_at(tpath, rvalue);
                    continue;
                }
                Expression::Variable { path, .. } => {
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
                        self.current_environment.update_value_at(tpath, rvalue);
                        continue;
                    } else if rtype == ExpressionType::NonPrimitive {
                        self.copy_or_move_elements(tpath.clone(), path.clone(), target_type, false);
                    }
                }
                Expression::Widen { operand, .. } => {
                    let rvalue = operand.widen(&tpath);
                    self.current_environment.update_value_at(tpath, rvalue);
                    continue;
                }
                _ => {}
            }
            if rtype != ExpressionType::NonPrimitive {
                self.current_environment.update_value_at(tpath, rvalue);
            }
            check_for_early_return!(self);
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
                        .filter(|(p, _)| p.is_rooted_by(&qualifier))
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
    #[logfn_inputs(DEBUG)]
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
                        let mut updated_value_map = self.current_environment.value_map.clone();
                        for (path, value) in self.current_environment.value_map.iter() {
                            if let Expression::Reference(p) = &value.expression {
                                if let PathEnum::HeapBlock { value } = &p.value {
                                    if let Expression::HeapBlock {
                                        abstract_address: a,
                                        is_zeroed: z,
                                    } = &value.expression
                                    {
                                        if *abstract_address == *a && *z {
                                            let new_block = AbstractValue::make_from(
                                                Expression::HeapBlock {
                                                    abstract_address: *a,
                                                    is_zeroed: false,
                                                },
                                                1,
                                            );
                                            let new_block_path = Path::get_as_path(new_block);
                                            let new_reference =
                                                AbstractValue::make_reference(new_block_path);
                                            updated_value_map = updated_value_map
                                                .insert(path.clone(), new_reference);
                                        }
                                    }
                                }
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
                let error = self.cv.session.struct_span_err(
                    self.current_span,
                    "the pointer points to memory that has already been deallocated",
                );
                self.emit_diagnostic(error);
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
                let error = self.cv.session.struct_span_err(self.current_span, &message);
                self.emit_diagnostic(error);
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

    /// Copies/moves all paths rooted in rpath to corresponding paths rooted in target_path.
    #[logfn_inputs(TRACE)]
    pub fn copy_or_move_elements(
        &mut self,
        target_path: Rc<Path>,
        source_path: Rc<Path>,
        target_rustc_type: Ty<'tcx>,
        move_elements: bool,
    ) {
        check_for_early_return!(self);
        // Some qualified source_paths are patterns that represent collections of values.
        // We need to expand the patterns before doing the actual moves.
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
                            debug!("PathSelector::ConstantIndex implies the length of the value is known");
                            assume_unreachable!();
                        }
                    } else {
                        u128::from(offset)
                    };
                    let index_val = self.get_u128_const_val(index);
                    let index_path = Path::new_index(qualifier.clone(), index_val)
                        .refine_paths(&self.current_environment);
                    self.copy_or_move_elements(
                        target_path,
                        index_path,
                        target_rustc_type,
                        move_elements,
                    );
                    return;
                }
                PathSelector::ConstantSlice { from, to, from_end } => {
                    self.copy_or_move_subslice(
                        target_path,
                        target_rustc_type,
                        move_elements,
                        qualifier,
                        from,
                        to,
                        from_end,
                    );
                    return;
                }
                _ => (),
            }
        };

        // Some target paths are wild card patterns and need to be dealt with via weak updates
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
                        self.weak_updates(qualifier, &source_path, |v| value.equals(v));
                        // and now fall through for a strong update of target_path
                    }
                }
                PathSelector::Slice(count) => {
                    // if the count is known at this point, expand it like a pattern.
                    if let Expression::CompileTimeConstant(ConstantDomain::U128(val)) =
                        &count.expression
                    {
                        self.copy_or_move_subslice(
                            qualifier.clone(),
                            target_rustc_type,
                            move_elements,
                            &source_path,
                            0,
                            *val as u32,
                            false,
                        );
                    } else {
                        //todo: just add target_path[0..count], lookup(source_path[0..count]) to the environment
                        //When that gets refined into a constant slice, then get back here.
                        // We do, however, have to havoc all of the existing bindings, conditionally,
                        // using index < count as the condition.
                    }
                    // fall through
                }
                _ => {
                    // fall through
                }
            }
        }

        // Get here for paths that are not patterns.
        let mut value_map = self.current_environment.value_map.clone();
        let is_closure = matches!(&target_rustc_type.kind, TyKind::Closure(..));
        let value = self.lookup_path_and_refine_result(source_path.clone(), target_rustc_type);
        let val_type = value.expression.infer_type();
        let mut no_children = true;
        if val_type == ExpressionType::NonPrimitive || is_closure {
            // First look at paths that are rooted in rpath.
            for (path, value) in self
                .current_environment
                .value_map
                .iter()
                .filter(|(p, _)| p.is_rooted_by(&source_path))
            {
                check_for_early_return!(self);
                let qualified_path = path.replace_root(&source_path, target_path.clone());
                if move_elements {
                    trace!("moving child {:?} to {:?}", value, qualified_path);
                    value_map = value_map.remove(path);
                } else {
                    trace!("copying child {:?} to {:?}", value, qualified_path);
                };
                value_map = value_map.insert(qualified_path, value.clone());
                no_children = false;
            }
        }
        let target_type: ExpressionType = (&target_rustc_type.kind).into();
        if target_type != ExpressionType::NonPrimitive || no_children {
            let value = self.lookup_path_and_refine_result(source_path.clone(), target_rustc_type);
            value_map =
                self.expand_aliased_string_literals(&target_path, target_type, value_map, &value);
            // Just copy/move (rpath, value) itself.
            if move_elements {
                trace!("moving {:?} to {:?}", value, target_path);
                value_map = value_map.remove(&source_path);
            } else {
                trace!("copying {:?} to {:?}", value, target_path);
            }
            self.current_environment.value_map = value_map;
            self.current_environment.update_value_at(target_path, value);
            return;
        }
        self.current_environment.value_map = value_map;
    }

    //from_end slice[from:-to] in Python terms.
    //otherwise slice[from:to]
    #[logfn_inputs(TRACE)]
    #[allow(clippy::too_many_arguments)]
    fn copy_or_move_subslice(
        &mut self,
        target_path: Rc<Path>,
        target_type: Ty<'tcx>,
        move_elements: bool,
        qualifier: &Rc<Path>,
        from: u32,
        to: u32,
        from_end: bool,
    ) {
        let to = {
            if from_end {
                let len_value = self.get_len(qualifier.clone());
                if let AbstractValue {
                    expression: Expression::CompileTimeConstant(ConstantDomain::U128(len)),
                    ..
                } = len_value.as_ref()
                {
                    u32::try_from(*len).unwrap() - to
                } else {
                    debug!("PathSelector::Subslice implies the length of the value is known");
                    assume_unreachable!();
                }
            } else {
                to
            }
        };
        let elem_size = self.type_visitor.get_elem_type_size(target_type);
        let length = self.get_u128_const_val(u128::from((to - from) as u64 * elem_size));
        let alignment = Rc::new(1u128.into());
        let slice_value = self.get_new_heap_block(length, alignment, false);
        self.current_environment
            .update_value_at(target_path.clone(), slice_value.clone());
        let slice_path = Rc::new(PathEnum::HeapBlock { value: slice_value }.into());
        let slice_len_path = Path::new_length(slice_path);
        let len_value = self.get_u128_const_val(u128::from(to - from));
        self.current_environment
            .update_value_at(slice_len_path, len_value);
        for i in from..to {
            let index_val = self.get_u128_const_val(u128::from(i));
            let index_path = Path::new_index(qualifier.clone(), index_val)
                .refine_paths(&self.current_environment);
            let target_index_val = self.get_u128_const_val(u128::try_from(i - from).unwrap());
            let indexed_target = Path::new_index(target_path.clone(), target_index_val)
                .refine_paths(&self.current_environment);
            self.copy_or_move_elements(indexed_target, index_path, target_type, move_elements);
            if self.assume_function_is_angelic {
                break;
            }
            check_for_early_return!(self);
        }
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

                new_value_map = new_value_map.insert(path.clone(), updated_value);
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

    // Check for assignment of a string literal to a byte array reference
    pub fn expand_aliased_string_literals(
        &mut self,
        target_path: &Rc<Path>,
        rtype: ExpressionType,
        mut value_map: HashTrieMap<Rc<Path>, Rc<AbstractValue>>,
        value: &Rc<AbstractValue>,
    ) -> HashTrieMap<Rc<Path>, Rc<AbstractValue>> {
        if rtype == ExpressionType::Reference {
            if let Expression::CompileTimeConstant(ConstantDomain::Str(s)) = &value.expression {
                if let PathEnum::LocalVariable { .. } = &target_path.value {
                    let lh_type = self
                        .type_visitor
                        .get_path_rustc_type(&target_path, self.current_span);
                    if let TyKind::Ref(_, ty, _) = lh_type.kind {
                        if let TyKind::Slice(elem_ty) = ty.kind {
                            if let TyKind::Uint(rustc_ast::ast::UintTy::U8) = elem_ty.kind {
                                let collection_path = Path::new_alias(value.clone());
                                for (i, ch) in s.as_bytes().iter().enumerate() {
                                    let index = Rc::new((i as u128).into());
                                    let ch_const = Rc::new((*ch as u128).into());
                                    let path = Path::new_index(collection_path.clone(), index)
                                        .refine_paths(&self.current_environment);
                                    value_map = value_map.insert(path, ch_const);
                                }
                            }
                        }
                    }
                }
            }
        }
        value_map
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
    ) -> Rc<AbstractValue> {
        let addresses = &mut self.heap_addresses;
        let constants = &mut self.cv.constant_value_cache;
        let block = addresses
            .entry(self.current_location)
            .or_insert_with(|| AbstractValue::make_from(constants.get_new_heap_block(is_zeroed), 1))
            .clone();
        let block_path = Path::get_as_path(block.clone());
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
}
