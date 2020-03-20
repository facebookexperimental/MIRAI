// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::abstract_value;
use crate::abstract_value::AbstractValue;
use crate::abstract_value::AbstractValueTrait;
use crate::constant_domain::{ConstantDomain, ConstantValueCache, FunctionReference};
use crate::environment::Environment;
use crate::expression::{Expression, ExpressionType, LayoutSource};
use crate::k_limits;
use crate::known_names::{KnownNames, KnownNamesCache};
use crate::options::{DiagLevel, Options};
use crate::path::PathRefinement;
use crate::path::{Path, PathEnum, PathSelector};
use crate::smt_solver::{SmtResult, SmtSolver};
use crate::summaries;
use crate::summaries::{PersistentSummaryCache, Precondition, Summary};
use crate::utils;

use log_derive::*;
use mirai_annotations::*;
use rpds::HashTrieMap;
use rustc::mir;
use rustc::mir::interpret::{ConstValue, Scalar};
use rustc::session::Session;
use rustc::ty::layout::VariantIdx;
use rustc::ty::subst::{GenericArg, GenericArgKind, InternalSubsts, SubstsRef};
use rustc::ty::{
    AdtDef, Const, ExistentialPredicate, ExistentialProjection, ExistentialTraitRef, FnSig,
    ParamTy, Ty, TyCtxt, TyKind, UserTypeAnnotationIndex,
};
use rustc_data_structures::graph::dominators::Dominators;
use rustc_errors::DiagnosticBuilder;
use rustc_hir::def_id::DefId;
use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;
use std::convert::TryInto;
use std::fmt::{Debug, Formatter, Result};
use std::io::Write;
use std::rc::Rc;
use std::time::Instant;

// 'compilation is the lifetime of compiler interface object supplied to the after_analysis call back.
// 'tcx is the lifetime of the type context created during the lifetime of the after_analysis call back.
// 'analysis is the life time of the analyze_with_mirai call back that is invoked with the type context.
pub struct MirVisitorCrateContext<'analysis, 'compilation, 'tcx, E> {
    pub options: &'compilation Options,
    pub session: &'compilation Session,
    pub tcx: TyCtxt<'tcx>,
    pub def_id: DefId,
    pub mir: mir::ReadOnlyBodyAndCache<'analysis, 'tcx>,
    pub constant_value_cache: &'analysis mut ConstantValueCache<'tcx>,
    pub known_names_cache: &'analysis mut KnownNamesCache,
    pub summary_cache: &'analysis mut PersistentSummaryCache<'tcx>,
    pub smt_solver: &'analysis mut dyn SmtSolver<E>,
    pub substs_cache: &'analysis mut HashMap<DefId, SubstsRef<'tcx>>,
    pub buffered_diagnostics: &'analysis mut Vec<DiagnosticBuilder<'compilation>>,
}

impl<'analysis, 'compilation, 'tcx, E> Debug
    for MirVisitorCrateContext<'analysis, 'compilation, 'tcx, E>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "MirVisitorCrateContext".fmt(f)
    }
}

/// Holds the state for the MIR test visitor.
pub struct MirVisitor<'analysis, 'compilation, 'tcx, E> {
    options: &'compilation Options,
    session: &'compilation Session,
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    mir: mir::ReadOnlyBodyAndCache<'analysis, 'tcx>,
    constant_value_cache: &'analysis mut ConstantValueCache<'tcx>,
    known_names_cache: &'analysis mut KnownNamesCache,
    summary_cache: &'analysis mut PersistentSummaryCache<'tcx>,
    smt_solver: &'analysis mut dyn SmtSolver<E>,
    substs_cache: &'analysis mut HashMap<DefId, SubstsRef<'tcx>>,
    buffered_diagnostics: &'analysis mut Vec<DiagnosticBuilder<'compilation>>,

    active_calls: Vec<DefId>,
    actual_argument_types: Vec<Ty<'tcx>>,
    already_reported_errors_for_call_to: HashSet<Rc<AbstractValue>>,
    // True if the current function cannot be analyzed and hence is just assumed to be correct.
    assume_function_is_angelic: bool,
    assume_preconditions_of_next_call: bool,
    async_fn_summary: Option<Summary>,
    check_for_errors: bool,
    check_for_unconditional_precondition: bool,
    current_environment: Environment,
    current_location: mir::Location,
    current_span: rustc_span::Span,
    start_instant: Instant,
    exit_environment: Environment,
    function_name: Rc<String>,
    generic_arguments: Option<SubstsRef<'tcx>>,
    generic_argument_map: Option<HashMap<rustc_span::Symbol, Ty<'tcx>>>,
    heap_addresses: HashMap<mir::Location, Rc<AbstractValue>>,
    path_ty_cache: HashMap<Rc<Path>, Ty<'tcx>>,
    post_condition: Option<Rc<AbstractValue>>,
    post_condition_block: Option<mir::BasicBlock>,
    preconditions: Vec<Precondition>,
    unwind_condition: Option<Rc<AbstractValue>>,
    unwind_environment: Environment,
    fresh_variable_offset: usize,
}

struct SavedVisitorState<'analysis, 'tcx> {
    def_id: DefId,
    mir: mir::ReadOnlyBodyAndCache<'analysis, 'tcx>,

    actual_argument_types: Vec<Ty<'tcx>>,
    already_reported_errors_for_call_to: HashSet<Rc<AbstractValue>>,
    assume_preconditions_of_next_call: bool,
    async_fn_summary: Option<Summary>,
    check_for_errors: bool,
    check_for_unconditional_precondition: bool,
    current_environment: Environment,
    current_location: mir::Location,
    current_span: rustc_span::Span,
    exit_environment: Environment,
    function_name: Rc<String>,
    fresh_variable_offset: usize,
    generic_arguments: Option<SubstsRef<'tcx>>,
    generic_argument_map: Option<HashMap<rustc_span::Symbol, Ty<'tcx>>>,
    heap_addresses: HashMap<mir::Location, Rc<AbstractValue>>,
    path_ty_cache: HashMap<Rc<Path>, Ty<'tcx>>,
    post_condition: Option<Rc<AbstractValue>>,
    post_condition_block: Option<mir::BasicBlock>,
    preconditions: Vec<Precondition>,
    unwind_condition: Option<Rc<AbstractValue>>,
    unwind_environment: Environment,
}

#[derive(Clone, Debug)]
struct CallInfo<'callinfo, 'tcx> {
    callee_def_id: DefId,
    callee_func_ref: Option<Rc<FunctionReference>>,
    callee_fun_val: Rc<AbstractValue>,
    callee_generic_arguments: Option<SubstsRef<'tcx>>,
    callee_known_name: KnownNames,
    callee_generic_argument_map: Option<HashMap<rustc_span::Symbol, Ty<'tcx>>>,
    actual_args: &'callinfo [(Rc<Path>, Rc<AbstractValue>)],
    actual_argument_types: &'callinfo [Ty<'tcx>],
    cleanup: Option<mir::BasicBlock>,
    destination: Option<(mir::Place<'tcx>, mir::BasicBlock)>,
    function_constant_args: &'callinfo [(Rc<Path>, Rc<AbstractValue>)],
}

impl<'callinfo, 'tcx> CallInfo<'callinfo, 'tcx> {
    fn new(
        callee_def_id: DefId,
        callee_generic_arguments: Option<SubstsRef<'tcx>>,
        callee_generic_argument_map: Option<HashMap<rustc_span::Symbol, Ty<'tcx>>>,
        func_const: ConstantDomain,
    ) -> CallInfo<'callinfo, 'tcx> {
        if let ConstantDomain::Function(func_ref) = &func_const {
            CallInfo {
                callee_def_id,
                callee_func_ref: Some(func_ref.clone()),
                callee_fun_val: Rc::new(func_const.into()),
                callee_generic_arguments,
                callee_known_name: KnownNames::None,
                callee_generic_argument_map,
                actual_args: &[],
                actual_argument_types: &[],
                cleanup: None,
                destination: None,
                function_constant_args: &[],
            }
        } else {
            unreachable!("caller should supply a constant function")
        }
    }
}

impl<'analysis, 'tcx> SavedVisitorState<'analysis, 'tcx> {
    pub fn new(
        def_id: DefId,
        mir: mir::ReadOnlyBodyAndCache<'analysis, 'tcx>,
    ) -> SavedVisitorState<'analysis, 'tcx> {
        SavedVisitorState {
            def_id,
            mir,
            actual_argument_types: vec![],
            already_reported_errors_for_call_to: HashSet::new(),
            assume_preconditions_of_next_call: false,
            async_fn_summary: None,
            check_for_errors: false,
            check_for_unconditional_precondition: false, // logging + new mir code gen breaks this for now
            current_environment: Environment::default(),
            current_location: mir::Location::START,
            current_span: rustc_span::DUMMY_SP,
            exit_environment: Environment::default(),
            function_name: Rc::new("".into()),
            fresh_variable_offset: 0,
            generic_arguments: None,
            generic_argument_map: None,
            heap_addresses: HashMap::default(),
            path_ty_cache: HashMap::default(),
            post_condition: None,
            post_condition_block: None,
            preconditions: Vec::new(),
            unwind_condition: None,
            unwind_environment: Environment::default(),
        }
    }
}

impl<'analysis, 'compilation, 'tcx, E> Debug for MirVisitor<'analysis, 'compilation, 'tcx, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "MirVisitor".fmt(f)
    }
}

/// If the currently analyzed function has been marked as angelic because was discovered
/// to do something that cannot be analyzed, or if the time taken to analyze the current
/// function exceeded k_limits::MAX_ANALYSIS_TIME_FOR_BODY, break out of the current loop.
/// When a timeout happens, currently analyzed function is marked as angelic.
macro_rules! check_for_early_break {
    ($sel:ident) => {
        if $sel.assume_function_is_angelic {
            break;
        }
        let elapsed_time_in_seconds = $sel.start_instant.elapsed().as_secs();
        if elapsed_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
            $sel.assume_function_is_angelic = true;
            break;
        }
    };
}

/// If the currently analyzed function has been marked as angelic because was discovered
/// to do something that cannot be analyzed, or if the time taken to analyze the current
/// function exceeded k_limits::MAX_ANALYSIS_TIME_FOR_BODY, return to the caller.
/// When a timeout happens, currently analyzed function is marked as angelic.
macro_rules! check_for_early_return {
    ($sel:ident) => {
        if $sel.assume_function_is_angelic {
            return;
        }
        let elapsed_time_in_seconds = $sel.start_instant.elapsed().as_secs();
        if elapsed_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
            $sel.assume_function_is_angelic = true;
            return;
        }
    };
}

/// A visitor that simply traverses enough of the MIR associated with a particular code body
/// so that we can test a call to every default implementation of the MirVisitor trait.
impl<'analysis, 'compilation, 'tcx, E> MirVisitor<'analysis, 'compilation, 'tcx, E> {
    #[logfn_inputs(TRACE)]
    pub fn new(
        crate_context: MirVisitorCrateContext<'analysis, 'compilation, 'tcx, E>,
    ) -> MirVisitor<'analysis, 'compilation, 'tcx, E> {
        let function_name = crate_context
            .summary_cache
            .get_summary_key_for(crate_context.def_id)
            .clone();
        MirVisitor {
            options: crate_context.options,
            session: crate_context.session,
            tcx: crate_context.tcx,
            def_id: crate_context.def_id,
            mir: crate_context.mir,
            constant_value_cache: crate_context.constant_value_cache,
            known_names_cache: crate_context.known_names_cache,
            summary_cache: crate_context.summary_cache,
            smt_solver: crate_context.smt_solver,
            substs_cache: crate_context.substs_cache,
            buffered_diagnostics: crate_context.buffered_diagnostics,

            active_calls: Vec::new(),
            actual_argument_types: vec![],
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
            exit_environment: Environment::default(),
            function_name,
            generic_arguments: None,
            generic_argument_map: None,
            heap_addresses: HashMap::default(),
            path_ty_cache: HashMap::default(),
            post_condition: None,
            post_condition_block: None,
            preconditions: Vec::new(),
            unwind_condition: None,
            unwind_environment: Environment::default(),
            fresh_variable_offset: 0,
        }
    }

    /// Restores the method only state to its initial state.
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
        self.exit_environment = Environment::default();
        self.generic_arguments = None;
        self.generic_argument_map = None;
        self.heap_addresses = HashMap::default();
        self.path_ty_cache = HashMap::default();
        self.post_condition = None;
        self.post_condition_block = None;
        self.preconditions = Vec::new();
        self.unwind_condition = None;
        self.unwind_environment = Environment::default();
        self.fresh_variable_offset = 1000;
    }

    fn swap_visitor_state(&mut self, saved_state: &mut SavedVisitorState<'analysis, 'tcx>) {
        std::mem::swap(&mut self.def_id, &mut saved_state.def_id);
        std::mem::swap(&mut self.mir, &mut saved_state.mir);
        std::mem::swap(
            &mut self.actual_argument_types,
            &mut saved_state.actual_argument_types,
        );
        std::mem::swap(
            &mut self.already_reported_errors_for_call_to,
            &mut saved_state.already_reported_errors_for_call_to,
        );
        std::mem::swap(
            &mut self.assume_preconditions_of_next_call,
            &mut saved_state.assume_preconditions_of_next_call,
        );
        std::mem::swap(
            &mut self.async_fn_summary,
            &mut saved_state.async_fn_summary,
        );
        std::mem::swap(
            &mut self.check_for_errors,
            &mut saved_state.check_for_errors,
        );
        std::mem::swap(
            &mut self.check_for_unconditional_precondition,
            &mut saved_state.check_for_unconditional_precondition,
        );
        std::mem::swap(
            &mut self.current_environment,
            &mut saved_state.current_environment,
        );
        std::mem::swap(
            &mut self.current_location,
            &mut saved_state.current_location,
        );
        std::mem::swap(&mut self.current_span, &mut saved_state.current_span);
        std::mem::swap(
            &mut self.exit_environment,
            &mut saved_state.exit_environment,
        );
        std::mem::swap(&mut self.function_name, &mut saved_state.function_name);
        std::mem::swap(
            &mut self.generic_arguments,
            &mut saved_state.generic_arguments,
        );
        std::mem::swap(
            &mut self.generic_argument_map,
            &mut saved_state.generic_argument_map,
        );
        std::mem::swap(&mut self.heap_addresses, &mut saved_state.heap_addresses);
        std::mem::swap(&mut self.path_ty_cache, &mut saved_state.path_ty_cache);
        std::mem::swap(&mut self.post_condition, &mut saved_state.post_condition);
        std::mem::swap(
            &mut self.post_condition_block,
            &mut saved_state.post_condition_block,
        );
        std::mem::swap(&mut self.preconditions, &mut saved_state.preconditions);
        std::mem::swap(
            &mut self.unwind_condition,
            &mut saved_state.unwind_condition,
        );
        std::mem::swap(
            &mut self.unwind_environment,
            &mut saved_state.unwind_environment,
        );
        std::mem::swap(
            &mut self.fresh_variable_offset,
            &mut saved_state.fresh_variable_offset,
        );
    }

    /// Analyze the body and store a summary of its behavior in self.summary_cache.
    /// Returns true if the newly computed summary is different from the summary (if any)
    /// that is already in the cache.
    #[logfn_inputs(TRACE)]
    pub fn visit_body(
        &mut self,
        function_constant_args: &[(Rc<Path>, Rc<AbstractValue>)],
    ) -> Summary {
        if cfg!(DEBUG) {
            let mut stdout = std::io::stdout();
            stdout.write_fmt(format_args!("{:?}", self.def_id)).unwrap();
            rustc_mir::util::write_mir_pretty(self.tcx, Some(self.def_id), &mut stdout).unwrap();
            info!("{:?}", stdout.flush());
        }
        self.active_calls.push(self.def_id);
        let (mut block_indices, contains_loop) = self.get_sorted_block_indices();

        let (mut in_state, mut out_state, mut terminator_state) =
            <MirVisitor<'analysis, 'compilation, 'tcx, E>>::initialize_state_maps(&block_indices);

        // The entry block has no predecessors and its initial state is the function parameters
        // (which we omit here so that we can lazily provision them with additional context)
        // as well any promoted constants.
        let mut first_state = self.promote_constants();

        // Add function constants.
        for (path, val) in function_constant_args.iter() {
            first_state.value_map = first_state.value_map.insert(path.clone(), val.clone())
        }

        let elapsed_time_in_seconds = self.compute_fixed_point(
            &mut block_indices,
            contains_loop,
            &mut in_state,
            &mut out_state,
            &mut terminator_state,
            &first_state,
        );

        if elapsed_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
            // This body is beyond MIRAI for now
            warn!(
                "analysis of {} timed out after {} seconds",
                self.function_name, elapsed_time_in_seconds,
            );
            self.active_calls.pop();
            return Summary::default();
        }

        if !self.assume_function_is_angelic {
            // Now traverse the blocks again, doing checks and emitting diagnostics.
            // terminator_state[bb] is now complete for every basic block bb in the body.
            self.check_for_errors(&block_indices, &mut terminator_state);
            self.active_calls.pop();

            // Now create a summary of the body that can be in-lined into call sites.
            if self.async_fn_summary.is_some() {
                self.preconditions = self.translate_async_preconditions();
                // todo: also translate side-effects, return result and post-condition
            };

            summaries::summarize(
                self.mir.arg_count,
                &self.exit_environment,
                &self.preconditions,
                &self.post_condition,
                self.unwind_condition.clone(),
                &self.unwind_environment,
                self.tcx,
            )
        } else {
            Summary::default()
        }
    }

    /// Summarize the referenced function, specialized by its generic arguments and the actual
    /// values of any function parameters. Then cache it.
    #[logfn_inputs(TRACE)]
    fn create_and_cache_function_summary(&mut self, call_info: &CallInfo<'_, 'tcx>) -> Summary {
        trace!(
            "summarizing {:?}: {:?}",
            call_info.callee_def_id,
            self.tcx.type_of(call_info.callee_def_id)
        );
        if self.tcx.is_mir_available(call_info.callee_def_id) {
            let elapsed_time = self.start_instant.elapsed();
            let mut saved_state = SavedVisitorState::new(self.def_id, self.mir);
            self.swap_visitor_state(&mut saved_state);
            self.def_id = call_info.callee_def_id;
            self.mir = self
                .tcx
                .optimized_mir(call_info.callee_def_id)
                .unwrap_read_only();
            self.actual_argument_types = call_info.actual_argument_types.into();
            self.generic_arguments = call_info.callee_generic_arguments;
            self.generic_argument_map = call_info.callee_generic_argument_map.clone();
            self.start_instant = Instant::now();
            self.function_name = self
                .summary_cache
                .get_summary_key_for(call_info.callee_def_id)
                .clone();
            let summary = self.visit_body(call_info.function_constant_args);
            trace!("summary {:?} {:?}", self.function_name, summary);
            if let Some(func_ref) = &call_info.callee_func_ref {
                // We cache the summary with call site details included so that
                // cached summaries are specialized with respect to call site generic arguments and
                // function constants arguments. Subsequent calls with the call site signature
                // will not need to re-summarize the function, thus avoiding exponential blow up.
                let signature =
                    self.get_function_constant_signature(call_info.function_constant_args);
                self.summary_cache
                    .set_summary_for_call_site(func_ref, signature, summary.clone());
            }
            self.swap_visitor_state(&mut saved_state);
            self.start_instant = Instant::now() - elapsed_time;
            return summary;
        } else if let Some(devirtualized_summary) = self.try_to_devirtualize(call_info) {
            return devirtualized_summary;
        }
        Summary::default()
    }

    /// If call_info.callee_def_id is a trait (virtual) then this tries to get the def_id of the
    /// concrete method that implements the given virtual method and returns the summary of that,
    /// computing it if necessary.
    #[logfn_inputs(TRACE)]
    fn try_to_devirtualize(&mut self, call_info: &CallInfo<'_, 'tcx>) -> Option<Summary> {
        let env_def_id = if self.tcx.is_closure(self.def_id) {
            self.tcx.closure_base_def_id(self.def_id)
        } else {
            self.def_id
        };
        if let Some(gen_args) = call_info.callee_generic_arguments {
            if !utils::are_concrete(gen_args) {
                trace!("non concrete generic args {:?}", gen_args);
                return None;
            }
            // The parameter environment of the caller provides a resolution context for the callee.
            let param_env = self.tcx.param_env(env_def_id);
            trace!(
                "devirtualize resolving def_id {:?}: {:?}",
                call_info.callee_def_id,
                self.tcx.type_of(call_info.callee_def_id)
            );
            trace!("gen_args {:?}", gen_args);
            if let Some(instance) =
                rustc::ty::Instance::resolve(self.tcx, param_env, call_info.callee_def_id, gen_args)
            {
                let resolved_def_id = instance.def.def_id();
                let resolved_ty = self.tcx.type_of(resolved_def_id);
                trace!(
                    "devirtualize resolved def_id {:?}: {:?}",
                    resolved_def_id,
                    resolved_ty
                );
                if !self.active_calls.contains(&resolved_def_id)
                    && self.tcx.is_mir_available(resolved_def_id)
                {
                    let func_ref = if let ConstantDomain::Function(fr) =
                        self.visit_function_reference(resolved_def_id, resolved_ty, instance.substs)
                    {
                        fr.clone()
                    } else {
                        unreachable!()
                    };
                    let cached_summary = self
                        .summary_cache
                        .get_summary_for_call_site(&func_ref, None);
                    if cached_summary.is_not_default {
                        return Some(cached_summary.clone());
                    }

                    let mut devirtualized_call_info = call_info.clone();
                    devirtualized_call_info.callee_def_id = resolved_def_id;
                    devirtualized_call_info.callee_func_ref = Some(func_ref);
                    devirtualized_call_info.callee_generic_arguments = Some(instance.substs);
                    devirtualized_call_info.callee_generic_argument_map = self
                        .get_generic_arguments_map(
                            resolved_def_id,
                            instance.substs,
                            call_info.actual_argument_types,
                        );
                    return Some(self.create_and_cache_function_summary(&devirtualized_call_info));
                } else {
                    return None;
                }
            }
        }
        None
    }

    /// Adds the given diagnostic builder to the buffer.
    /// Buffering diagnostics gives us the chance to sort them before printing them out,
    /// which is desirable for tools that compare the diagnostics from one run of MIRAI with another.
    #[logfn_inputs(TRACE)]
    fn emit_diagnostic(&mut self, mut diagnostic_builder: DiagnosticBuilder<'compilation>) {
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

    /// Use the local and global environments to resolve Path to an abstract value.
    #[logfn_inputs(TRACE)]
    fn lookup_path_and_refine_result(
        &mut self,
        path: Rc<Path>,
        result_type: ExpressionType,
    ) -> Rc<AbstractValue> {
        match &path.value {
            PathEnum::Constant { value } => {
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
                    let refined_val = self.lookup_path_and_refine_result(path, result_type.clone());
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
                let mut result = None;
                if result_type == ExpressionType::Reference {
                    // This could be an alias for a fat pointer stored at path.0 (etc.)
                    for (leaf_path, val) in self.current_environment.value_map.iter() {
                        if leaf_path.is_first_leaf_rooted_in(&path) {
                            result = Some(val.clone());
                            break;
                        }
                    }
                }
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
                                ExpressionType::NonPrimitive,
                            );
                            debug!("qualifier_val {:?}", qualifier_val);
                            if qualifier_val.is_contained_in_zeroed_heap_block() {
                                result = Some(Rc::new(
                                    if result_type.is_signed_integer() {
                                        self.constant_value_cache.get_i128_for(0)
                                    } else {
                                        self.constant_value_cache.get_u128_for(0)
                                    }
                                    .clone()
                                    .into(),
                                ))
                            }
                        }
                    }
                }
                result.unwrap_or_else(|| {
                    let result = AbstractValue::make_from(
                        Expression::Variable {
                            path: path.clone(),
                            var_type: result_type.clone(),
                        },
                        1,
                    );
                    if result_type != ExpressionType::NonPrimitive {
                        self.current_environment
                            .update_value_at(path, result.clone());
                    }
                    result
                })
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
        let summary;
        let summary = if let Some(def_id) = def_id {
            let generic_args = self.substs_cache.get(&def_id).cloned();
            let callee_generic_argument_map = if let Some(generic_args) = generic_args {
                self.get_generic_arguments_map(def_id, generic_args, &[])
            } else {
                None
            };
            let ty = self.tcx.type_of(def_id);
            let func_const = self
                .constant_value_cache
                .get_function_constant_for(
                    def_id,
                    ty,
                    generic_args.unwrap_or_else(|| self.tcx.empty_substs_for_def_id(def_id)),
                    self.tcx,
                    self.known_names_cache,
                    self.summary_cache,
                )
                .clone();
            let call_info = CallInfo::new(
                def_id,
                generic_args,
                callee_generic_argument_map,
                func_const,
            );
            let func_ref = call_info
                .callee_func_ref
                .clone()
                .expect("CallInfo::new should guarantee this");
            let cached_summary = self
                .summary_cache
                .get_summary_for_call_site(&func_ref, None);
            if cached_summary.is_not_default {
                cached_summary
            } else {
                summary = self.create_and_cache_function_summary(&call_info);
                &summary
            }
        } else {
            summary = self
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
                AbstractValue::make_from(
                    Expression::Variable {
                        path: path.clone(),
                        var_type: expression_type.clone(),
                    },
                    1,
                )
            })
    }

    /// Path is required to be rooted in a temporary used to track a checked operation result.
    /// The result type of the local will be a tuple (t, bool).
    /// The result of this function is the t part.
    #[logfn_inputs(TRACE)]
    fn get_first_part_of_target_path_type_tuple(&mut self, path: &Rc<Path>) -> ExpressionType {
        match &self.get_path_rustc_type(path).kind {
            TyKind::Tuple(types) => (&types[0].expect_ty().kind).into(),
            _ => assume_unreachable!(),
        }
    }

    // Path is required to be rooted in a temporary used to track an operation result.
    #[logfn_inputs(TRACE)]
    fn get_target_path_type(&mut self, path: &Rc<Path>) -> ExpressionType {
        (&self.get_path_rustc_type(path).kind).into()
    }

    /// Lookups up the local definition for this ordinal and maps the type information
    /// onto ExpressionType.
    #[logfn_inputs(TRACE)]
    fn get_type_for_local(&self, ordinal: usize) -> ExpressionType {
        let loc = &self.mir.local_decls[mir::Local::from(ordinal)];
        (&loc.ty.kind).into()
    }

    /// Do a topological sort, breaking loops by preferring lower block indices, using dominance
    /// to determine if there is a loop (if a is predecessor of b and b dominates a then they
    /// form a loop and we'll emit the one with the lower index first).
    #[logfn_inputs(TRACE)]
    fn add_predecessors_then_root_block(
        &self,
        root_block: mir::BasicBlock,
        dominators: &Dominators<mir::BasicBlock>,
        contains_loop: &mut bool,
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
                *contains_loop = true;
                continue;
            }
            self.add_predecessors_then_root_block(
                *pred_bb,
                dominators,
                contains_loop,
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
    fn get_sorted_block_indices(&mut self) -> (Vec<mir::BasicBlock>, bool) {
        let dominators = self.mir.dominators();
        let mut block_indices = Vec::new();
        let mut already_added = HashSet::new();
        let mut contains_loop = false;
        for bb in self.mir.basic_blocks().indices() {
            self.add_predecessors_then_root_block(
                bb,
                &dominators,
                &mut contains_loop,
                &mut block_indices,
                &mut already_added,
            );
        }
        (block_indices, contains_loop)
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
            Path::new_field(closure_path.clone(), 0, &self.current_environment),
            &self.current_environment,
        );
        let discriminant_val = Rc::new(self.constant_value_cache.get_u128_for(0).clone().into());

        // Populate the closure object fields with the parameters and locals of the current context.
        self.current_environment
            .update_value_at(discriminant, discriminant_val);
        for (i, loc) in self.mir.local_decls.iter().skip(1).enumerate() {
            let qualifier = closure_path.clone();
            let closure_path = Path::new_field(
                Path::new_field(qualifier, 0, &self.current_environment),
                i,
                &self.current_environment,
            );
            // skip(1) above ensures this
            assume!(i < usize::max_value());
            let path = if i < self.mir.arg_count {
                Path::new_parameter(i + 1)
            } else {
                Path::new_local(i + 1)
            };
            let ty: ExpressionType = (&loc.ty.kind).into();
            let value = self.lookup_path_and_refine_result(path, ty);
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

    /// Compute a fixed point, which is a value of out_state that will not grow with more iterations.
    #[logfn_inputs(TRACE)]
    fn compute_fixed_point(
        &mut self,
        mut block_indices: &mut Vec<mir::BasicBlock>,
        contains_loop: bool,
        mut in_state: &mut HashMap<mir::BasicBlock, Environment>,
        mut out_state: &mut HashMap<mir::BasicBlock, Environment>,
        mut terminator_state: &mut HashMap<mir::BasicBlock, Environment>,
        first_state: &Environment,
    ) -> u64 {
        let mut iteration_count = 0;
        let mut changed = true;
        while changed {
            self.fresh_variable_offset = 0;
            changed = self.visit_blocks(
                &mut block_indices,
                &mut in_state,
                &mut out_state,
                &mut terminator_state,
                &first_state,
                iteration_count,
            );
            if !contains_loop {
                break;
            }
            check_for_early_break!(self);
            if iteration_count > k_limits::MAX_FIXPOINT_ITERATIONS {
                break;
            }
            iteration_count += 1;
        }
        if iteration_count > 10 {
            warn!(
                "Fixed point loop took {} iterations for {}.",
                iteration_count, self.function_name
            );
        } else {
            trace!(
                "Fixed point loop took {} iterations for {}.",
                iteration_count,
                self.function_name
            );
        }
        self.start_instant.elapsed().as_secs()
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
    }

    #[logfn_inputs(TRACE)]
    fn initialize_state_maps(
        block_indices: &[mir::BasicBlock],
    ) -> (
        HashMap<mir::BasicBlock, Environment>,
        HashMap<mir::BasicBlock, Environment>,
        HashMap<mir::BasicBlock, Environment>,
    ) {
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
        (in_state, out_state, terminator_state)
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
        terminator_state: &mut HashMap<mir::BasicBlock, Environment>,
        first_state: &Environment,
        iteration_count: usize,
    ) -> bool {
        let mut changed = false;
        for bb in block_indices.iter() {
            check_for_early_break!(self);

            // Merge output states of predecessors of bb
            let i_state = if bb.index() == 0 {
                first_state.clone()
            } else {
                self.get_initial_state_from_predecessors(*bb, in_state, out_state, iteration_count)
            };
            // Analyze the basic block
            in_state.insert(*bb, i_state.clone());
            self.current_environment = i_state;
            self.visit_basic_block(*bb, terminator_state);

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
            // Remove predecessors that cannot reach this block
            predecessor_states_and_conditions = predecessor_states_and_conditions
                .into_iter()
                .filter(|(_, pred_exit_condition)| {
                    if let Some(cond) = pred_exit_condition {
                        cond.as_bool_if_known().unwrap_or(true)
                    } else {
                        false
                    }
                })
                .collect();
            if predecessor_states_and_conditions.is_empty() {
                let mut i_state = in_state[&bb].clone();
                i_state.entry_condition = Rc::new(abstract_value::FALSE);
                return i_state;
            }
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
    fn promote_constants(&mut self) -> Environment {
        let mut environment = Environment::default();
        let saved_mir = self.mir;
        let result_root: Rc<Path> = Path::new_result();
        for (ordinal, constant_mir) in self.tcx.promoted_mir(self.def_id).iter().enumerate() {
            self.mir = constant_mir.unwrap_read_only();
            let result_type = self.get_type_for_local(0);
            self.visit_promoted_constants_block();

            let promoted_root: Rc<Path> = Rc::new(PathEnum::PromotedConstant { ordinal }.into());
            let value = self.lookup_path_and_refine_result(result_root.clone(), result_type);
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
                        .value_map
                        .iter()
                        .filter(|(p, _)| p.is_rooted_by(&result_root))
                    {
                        let promoted_path = path.replace_root(&result_root, promoted_root.clone());
                        environment.update_value_at(promoted_path, value.clone());
                    }
                    if let Expression::Variable { .. } = &value.expression {
                        // The constant is a stack allocated struct. No need for a separate entry.
                    } else {
                        environment.update_value_at(promoted_root.clone(), value.clone());
                    }
                }
            }
            self.reset_visitor_state();
        }
        self.mir = saved_mir;
        environment
    }

    /// Computes a fixed point over the blocks of the MIR for a promoted constant block
    #[logfn_inputs(TRACE)]
    fn visit_promoted_constants_block(&mut self) {
        let (mut block_indices, contains_loop) = self.get_sorted_block_indices();

        let (mut in_state, mut out_state, mut terminator_state) =
            <MirVisitor<'analysis, 'compilation, 'tcx, E>>::initialize_state_maps(&block_indices);

        // The entry block has no predecessors and its initial state is the function parameters
        // (which we omit here so that we can lazily provision them with additional context).
        let first_state = Environment::default();

        self.compute_fixed_point(
            &mut block_indices,
            contains_loop,
            &mut in_state,
            &mut out_state,
            &mut terminator_state,
            &first_state,
        );

        self.check_for_errors(&block_indices, &mut terminator_state);
    }

    /// Visits each statement in order and then visits the terminator.
    #[logfn_inputs(TRACE)]
    fn visit_basic_block(
        &mut self,
        bb: mir::BasicBlock,
        terminator_state: &mut HashMap<mir::BasicBlock, Environment>,
    ) {
        let mir::BasicBlockData {
            ref statements,
            ref terminator,
            ..
        } = &self.mir[bb];
        let mut location = bb.start_location();
        let terminator_index = statements.len();

        if !self.check_for_errors {
            while location.statement_index < terminator_index {
                self.visit_statement(location, &statements[location.statement_index]);
                check_for_early_return!(self);
                location.statement_index += 1;
            }
            terminator_state.insert(bb, self.current_environment.clone());
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
        trace!("env {:?}", self.current_environment);
        self.current_location = location;
        let mir::Statement { kind, source_info } = statement;
        self.current_span = source_info.span;
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
            mir::StatementKind::InlineAsm(inline_asm) => self.visit_inline_asm(inline_asm),
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
        variant_index: rustc::ty::layout::VariantIdx,
    ) {
        let target_path =
            Path::new_discriminant(self.visit_place(place), &self.current_environment);
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
        let path = Path::new_local_parameter_or_result(local.as_usize(), self.mir.arg_count);
        self.current_environment
            .update_value_at(path, abstract_value::BOTTOM.into());
    }

    /// Execute a piece of inline Assembly.
    #[logfn_inputs(TRACE)]
    fn visit_inline_asm(&mut self, inline_asm: &mir::InlineAsm<'tcx>) {
        let span = self.current_span;
        let err = self.session.struct_span_warn(
            span,
            "Inline assembly code cannot be analyzed by MIRAI. Unsoundly ignoring this.",
        );
        self.emit_diagnostic(err);
        self.assume_function_is_angelic = true;
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
        trace!("env {:?}", self.current_environment);
        self.current_location = location;
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

    /// Indicates a normal return. The return place should have
    /// been filled in by now. This should occur at most once.
    #[logfn_inputs(TRACE)]
    fn visit_return(&mut self) {
        if self.check_for_errors {
            // Done with fixed point, so prepare to summarize.
            if self.post_condition.is_none() && !self.current_environment.entry_condition.is_top() {
                let return_guard = self.current_environment.entry_condition.as_bool_if_known();
                if return_guard.is_none() {
                    self.post_condition = Some(self.current_environment.entry_condition.clone());
                }
            }
            // When the summary is prepared the current environment might be different, so remember this one.
            self.exit_environment = self.current_environment.clone();
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

        trace!("visit_call {:?} {:?}", func, args);
        trace!("self.generic_argument_map {:?}", self.generic_argument_map);
        trace!("env {:?}", self.current_environment);
        let func_to_call = self.visit_operand(func);
        let func_ref = self.get_func_ref(&func_to_call);
        let func_ref_to_call;
        if let Some(fr) = func_ref {
            func_ref_to_call = fr;
        } else {
            self.report_missing_summary();
            info!(
                "function {} can't be reliably analyzed because it calls an unknown function.",
                utils::summary_key_str(self.tcx, self.def_id),
            );
            return;
        }
        let callee_def_id = func_ref_to_call
            .def_id
            .expect("callee obtained via operand should have def id");
        let substs = self
            .substs_cache
            .get(&callee_def_id)
            .expect("MIR should ensure this");
        let callee_generic_arguments = self.specialize_substs(substs, &self.generic_argument_map);
        let actual_args: Vec<(Rc<Path>, Rc<AbstractValue>)> = args
            .iter()
            .map(|arg| (self.get_operand_path(arg), self.visit_operand(arg)))
            .collect();
        let actual_argument_types: Vec<Ty<'tcx>> = args
            .iter()
            .map(|arg| {
                let arg_ty = self.get_operand_rustc_type(arg);
                self.specialize_generic_argument_type(arg_ty, &self.generic_argument_map)
            })
            .collect();
        let callee_generic_argument_map = self.get_generic_arguments_map(
            callee_def_id,
            callee_generic_arguments,
            &actual_argument_types,
        );

        let call_info = CallInfo {
            callee_def_id,
            callee_known_name: func_ref_to_call.known_name,
            callee_func_ref: Some(func_ref_to_call.clone()),
            callee_fun_val: func_to_call,
            callee_generic_arguments: Some(callee_generic_arguments),
            callee_generic_argument_map,
            actual_args: &actual_args,
            actual_argument_types: &actual_argument_types,
            cleanup,
            destination: *destination,
            function_constant_args: &self.get_function_constant_args(&actual_args),
        };
        debug!("calling func {:?}", call_info);
        if self.handled_as_special_function_call(&call_info) {
            return;
        }
        let function_summary = self
            .get_function_summary(&call_info)
            .unwrap_or_else(Summary::default);
        if self.check_for_errors && !function_summary.is_not_default {
            self.deal_with_missing_summary(&call_info);
        }
        debug!(
            "summary {:?} {:?}",
            func_ref_to_call.summary_cache_key, function_summary
        );
        debug!("pre env {:?}", self.current_environment);
        self.check_preconditions_if_necessary(&call_info, &function_summary);
        self.transfer_and_refine_normal_return_state(&call_info, &function_summary);
        self.transfer_and_refine_cleanup_state(&call_info, &function_summary);
        debug!("post env {:?}", self.current_environment);
        if function_summary.post_condition.is_some() {
            if let Some((_, b)) = &call_info.destination {
                debug!(
                    "post exit conditions {:?}",
                    self.current_environment.exit_conditions.get(b)
                );
            }
        }
    }

    #[logfn_inputs(TRACE)]
    fn get_function_constant_args(
        &self,
        actual_args: &[(Rc<Path>, Rc<AbstractValue>)],
    ) -> Vec<(Rc<Path>, Rc<AbstractValue>)> {
        let mut result = vec![];
        for (path, value) in self.current_environment.value_map.iter() {
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
            if let PathEnum::Constant { value: val } = &path.value {
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

    /// Extract a list of function references from an environment of function constant arguments
    #[logfn_inputs(TRACE)]
    fn get_function_constant_signature(
        &mut self,
        func_args: &[(Rc<Path>, Rc<AbstractValue>)],
    ) -> Option<Vec<Rc<FunctionReference>>> {
        if func_args.is_empty() {
            return None;
        }
        let vec: Vec<Rc<FunctionReference>> = func_args
            .iter()
            .filter_map(|(_, v)| self.get_func_ref(v))
            .collect();
        if vec.is_empty() {
            return None;
        }
        Some(vec)
    }

    /// Give diagnostic or mark the call chain as angelic, depending on self.options.diag_level
    #[logfn_inputs(TRACE)]
    fn deal_with_missing_summary(&mut self, call_info: &CallInfo<'_, 'tcx>) {
        self.report_missing_summary();
        let argument_type_hint = if let Some(func) = &call_info.callee_func_ref {
            format!(" (foreign fn argument key: {})", func.argument_type_key)
        } else {
            "".to_string()
        };
        info!(
            "function {} can't be reliably analyzed because it calls function {} which has no body and no summary{}.",
            utils::summary_key_str(self.tcx, self.def_id),
            utils::summary_key_str(self.tcx, call_info.callee_def_id),
            argument_type_hint,
        );
        debug!("def_id {:?}", call_info.callee_def_id);
    }

    /// Give diagnostic, depending on self.options.diag_level
    #[logfn_inputs(TRACE)]
    fn report_missing_summary(&mut self) {
        match self.options.diag_level {
            DiagLevel::RELAXED => {
                // Assume the callee is perfect and assume the caller and all of its callers are perfect
                // little angels as well. This cuts down on false positives caused by missing post
                // conditions.
                self.assume_function_is_angelic = true;
            }
            DiagLevel::STRICT => {
                // Assume the callee is perfect and that the caller does not need to prove any
                // preconditions and that the callee guarantees no post conditions.
            }
            DiagLevel::PARANOID => {
                if self.check_for_errors {
                    // Give a diagnostic about this call, and make it the programmer's problem.
                    let error = self.session.struct_span_err(
                        self.current_span,
                        "the called function has no body and has not been summarized, all bets are off",
                    );
                    self.emit_diagnostic(error);
                }
            }
        }
    }

    /// Returns a summary of the function to call, obtained from the summary cache.
    #[logfn_inputs(TRACE)]
    fn get_function_summary(&mut self, call_info: &CallInfo<'_, 'tcx>) -> Option<Summary> {
        if let Some(func_ref) = self.get_func_ref(&call_info.callee_fun_val) {
            // If the actual arguments include any function constants, collect them together
            // and pass them to get_summary_for_function_constant so that their signatures
            // can be included in the type specific key that is used to look up non generic
            // predefined summaries.
            let func_args: Option<Vec<Rc<FunctionReference>>> =
                if !call_info.function_constant_args.is_empty() {
                    Some(
                        call_info
                            .function_constant_args
                            .iter()
                            .filter_map(|(_, v)| self.get_func_ref(v))
                            .collect(),
                    )
                } else {
                    // common case
                    None
                };
            let result = self
                .summary_cache
                .get_summary_for_call_site(&func_ref, func_args)
                .clone();
            if result.is_not_default || func_ref.def_id.is_none() {
                return Some(result);
            }
            if !self.active_calls.contains(&func_ref.def_id.unwrap()) {
                return Some(self.create_and_cache_function_summary(call_info));
            }
        }
        None
    }

    /// Returns the function reference part of the value, if there is one.
    #[logfn_inputs(TRACE)]
    fn get_func_ref(&mut self, val: &Rc<AbstractValue>) -> Option<Rc<FunctionReference>> {
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
                var_type: ExpressionType::Reference,
            } => {
                let closure_ty = self.get_path_rustc_type(path);
                match closure_ty.kind {
                    TyKind::Closure(def_id, substs) => {
                        let specialized_substs =
                            self.specialize_substs(substs, &self.generic_argument_map);
                        return extract_func_ref(self.visit_function_reference(
                            def_id,
                            closure_ty,
                            specialized_substs,
                        ));
                    }
                    TyKind::Ref(_, ty, _) => {
                        if let TyKind::Closure(def_id, substs) = ty.kind {
                            let specialized_substs =
                                self.specialize_substs(substs, &self.generic_argument_map);
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

    /// Extracts the def_id of a closure, given the type of a value that is known to be a closure.
    /// Returns None otherwise.
    #[logfn_inputs(TRACE)]
    fn get_def_id_from_closure(&mut self, closure_ty: Ty<'tcx>) -> Option<DefId> {
        match closure_ty.kind {
            TyKind::Closure(def_id, _) => {
                return Some(def_id);
            }
            TyKind::Ref(_, ty, _) => {
                if let TyKind::Closure(def_id, _) = ty.kind {
                    return Some(def_id);
                }
            }
            _ => {}
        }
        None
    }

    /// If we are checking for errors and have not assumed the preconditions of the called function
    /// and we are not in angelic mode and have not already reported an error for this call,
    /// then check the preconditions and report any conditions that are not known to hold at this point.
    #[logfn_inputs(TRACE)]
    fn check_preconditions_if_necessary(
        &mut self,
        call_info: &CallInfo<'_, 'tcx>,
        function_summary: &Summary,
    ) {
        if self.check_for_errors
            && !self.assume_preconditions_of_next_call
            && !self
                .already_reported_errors_for_call_to
                .contains(&call_info.callee_fun_val)
        {
            self.check_function_preconditions(call_info, function_summary);
        } else {
            self.assume_preconditions_of_next_call = false;
        }
    }

    /// If the current call is to a well known function for which we don't have a cached summary,
    /// this function will update the environment as appropriate and return true. If the return
    /// result is false, just carry on with the normal logic.
    #[logfn_inputs(TRACE)]
    fn handled_as_special_function_call(&mut self, call_info: &CallInfo<'_, 'tcx>) -> bool {
        match call_info.callee_known_name {
            KnownNames::StdOpsFunctionFnCall
            | KnownNames::StdOpsFunctionFnMutCallMut
            | KnownNames::StdOpsFunctionFnOnceCallOnce => {
                return !self
                    .try_to_inline_indirectly_called_function(call_info)
                    .is_bottom();
            }
            KnownNames::MiraiAbstractValue => {
                checked_assume!(call_info.actual_args.len() == 1);
                self.handle_abstract_value(call_info);
                return true;
            }
            KnownNames::MiraiAssume => {
                checked_assume!(call_info.actual_args.len() == 1);
                if self.check_for_errors {
                    self.report_calls_to_special_functions(call_info);
                }
                self.handle_assume(call_info);
                return true;
            }
            KnownNames::MiraiAssumePreconditions => {
                checked_assume!(call_info.actual_args.is_empty());
                self.assume_preconditions_of_next_call = true;
                return true;
            }
            KnownNames::MiraiGetModelField => {
                self.handle_get_model_field(call_info);
                return true;
            }
            KnownNames::MiraiPostcondition => {
                checked_assume!(call_info.actual_args.len() == 3);
                if self.check_for_errors {
                    self.report_calls_to_special_functions(call_info);
                }
                self.handle_post_condition(call_info);
                return true;
            }
            KnownNames::MiraiPreconditionStart => {
                self.handle_precondition_start(call_info);
                return true;
            }
            KnownNames::MiraiPrecondition => {
                checked_assume!(call_info.actual_args.len() == 2);
                self.handle_precondition(call_info);
                self.handle_assume(call_info);
                return true;
            }
            KnownNames::MiraiSetModelField => {
                self.handle_set_model_field(call_info);
                return true;
            }
            KnownNames::MiraiShallowClone => {
                if let Some((place, target)) = &call_info.destination {
                    checked_assume!(call_info.actual_args.len() == 1);
                    let source_path = call_info.actual_args[0].0.clone();
                    let target_type = self.get_rustc_place_type(place);
                    let target_path = self.visit_place(place);
                    self.copy_or_move_elements(target_path, source_path, target_type, false);
                    let exit_condition = self.current_environment.entry_condition.clone();
                    self.current_environment.exit_conditions = self
                        .current_environment
                        .exit_conditions
                        .insert(*target, exit_condition);
                } else {
                    assume_unreachable!();
                }
                return true;
            }
            KnownNames::MiraiResult => {
                if let Some((place, target)) = &call_info.destination {
                    let target_path = self.visit_place(place);
                    let target_type = self.get_place_type(place);
                    let return_value_path = Path::new_result();
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
                    assume_unreachable!();
                }
                return true;
            }
            KnownNames::MiraiVerify => {
                checked_assume!(call_info.actual_args.len() == 2);
                if self.check_for_errors {
                    self.report_calls_to_special_functions(call_info);
                }
                let mut call_info = call_info.clone();
                call_info.actual_args = &call_info.actual_args[0..1];
                self.handle_assume(&call_info);
                return true;
            }
            KnownNames::RustDealloc => {
                self.handle_rust_dealloc(call_info);
                if let Some((_, target)) = &call_info.destination {
                    let exit_condition = self.current_environment.entry_condition.clone();
                    self.current_environment.exit_conditions = self
                        .current_environment
                        .exit_conditions
                        .insert(*target, exit_condition);
                } else {
                    assume_unreachable!("a call to __rust_dealloc should have a target block");
                }
                return true;
            }
            KnownNames::StdFutureFromGenerator => {
                checked_assume!(call_info.actual_args.len() == 1);
                let mut call_info = call_info.clone();
                call_info.callee_fun_val = call_info.actual_args[0].1.clone();
                call_info.callee_func_ref = self.get_func_ref(&call_info.callee_fun_val);
                call_info.callee_def_id = call_info
                    .callee_func_ref
                    .clone()
                    .expect("a fun ref")
                    .def_id
                    .expect("a def id");
                call_info.actual_args = &[];
                call_info.actual_argument_types = &[];
                call_info.callee_generic_arguments = None;
                self.async_fn_summary = self.get_function_summary(&call_info);
                return true;
            }
            KnownNames::StdIntrinsicsCopyNonOverlapping => {
                self.handle_copy_non_overlapping(call_info);
                if let Some((_, target)) = &call_info.destination {
                    let exit_condition = self.current_environment.entry_condition.clone();
                    self.current_environment.exit_conditions = self
                        .current_environment
                        .exit_conditions
                        .insert(*target, exit_condition);
                }
                return true;
            }
            KnownNames::StdPanickingBeginPanic | KnownNames::StdPanickingBeginPanicFmt => {
                if self.check_for_errors {
                    self.report_calls_to_special_functions(call_info); //known_name, actual_args);
                }
                if let Some((_, target)) = &call_info.destination {
                    self.current_environment.exit_conditions = self
                        .current_environment
                        .exit_conditions
                        .insert(*target, abstract_value::FALSE.into());
                }
                return true;
            }
            _ => {
                let result = self.try_to_inline_special_function(call_info);
                if !result.is_bottom() {
                    if let Some((place, target)) = &call_info.destination {
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

    /// Replace the call result with an abstract value of the same type as the
    /// destination place.
    #[logfn_inputs(TRACE)]
    fn handle_abstract_value(&mut self, call_info: &CallInfo<'_, 'tcx>) {
        if let Some((place, target)) = &call_info.destination {
            let path = self.visit_place(place);
            let expression_type = self.get_place_type(place);
            let abstract_value = AbstractValue::make_from(
                Expression::Variable {
                    path: path.clone(),
                    var_type: expression_type,
                },
                1,
            );
            self.current_environment
                .update_value_at(path, abstract_value);
            let exit_condition = self.current_environment.entry_condition.clone();
            self.current_environment.exit_conditions = self
                .current_environment
                .exit_conditions
                .insert(*target, exit_condition);
        } else {
            assume_unreachable!();
        }
    }

    /// Update the state so that the call result is the value of the model field (or the default
    /// value if there is no field).
    #[logfn_inputs(TRACE)]
    fn handle_get_model_field(&mut self, call_info: &CallInfo<'_, 'tcx>) {
        if let Some((place, target)) = &call_info.destination {
            let target_type = self.get_rustc_place_type(place);
            checked_assume!(call_info.actual_args.len() == 3);

            // The current value, if any, of the model field are a set of (path, value) pairs
            // where each path is rooted by qualifier.model_field(..)
            let qualifier = call_info.actual_args[0].0.clone();
            let field_name = self.coerce_to_string(&call_info.actual_args[1].1);
            let source_path =
                Path::new_model_field(qualifier, field_name, &self.current_environment)
                    .refine_paths(&self.current_environment);

            let target_path = self.visit_place(place);
            if self.current_environment.value_at(&source_path).is_some() {
                // Move the model field (path, val) pairs to the target (i.e. the place where
                // the return value of call to the mirai_get_model_field function would go if
                // it were a normal call.
                self.copy_or_move_elements(target_path, source_path, target_type, true);
            } else {
                // If there is no value for the model field in the environment, we should
                // use the default value, but only if the qualifier is not rooted in a parameter
                // value since only the caller will know what the values of the fields are.
                match &call_info.actual_args[0].1.expression {
                    Expression::Reference(path) | Expression::Variable { path, .. }
                        if path.is_rooted_by_parameter() =>
                    {
                        //todo: if the default value is a non primitive then we lose the structure
                        // using the code below. That is wrong. Generalize the default field.
                        let rval = AbstractValue::make_from(
                            Expression::UnknownModelField {
                                path: source_path,
                                default: call_info.actual_args[2].1.clone(),
                            },
                            1,
                        );
                        self.current_environment.update_value_at(target_path, rval);
                    }
                    _ => {
                        let source_path = call_info.actual_args[2].0.clone();
                        self.copy_or_move_elements(target_path, source_path, target_type, true);
                    }
                }
            }
            let exit_condition = self.current_environment.entry_condition.clone();
            self.current_environment.exit_conditions = self
                .current_environment
                .exit_conditions
                .insert(*target, exit_condition);
        } else {
            assume_unreachable!();
        }
    }

    /// Update the state to reflect the assignment of the model field.
    #[logfn_inputs(TRACE)]
    fn handle_set_model_field(&mut self, call_info: &CallInfo<'_, 'tcx>) {
        checked_assume!(call_info.actual_args.len() == 3);
        if let Some((_, target)) = &call_info.destination {
            let qualifier = call_info.actual_args[0].0.clone();
            let field_name = self.coerce_to_string(&call_info.actual_args[1].1);
            let target_path =
                Path::new_model_field(qualifier, field_name, &self.current_environment);
            let source_path = call_info.actual_args[2].0.clone();
            let target_type = call_info.actual_argument_types[2];
            self.copy_or_move_elements(target_path, source_path, target_type, true);
            let exit_condition = self.current_environment.entry_condition.clone();
            self.current_environment.exit_conditions = self
                .current_environment
                .exit_conditions
                .insert(*target, exit_condition);
        } else {
            assume_unreachable!();
        }
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
                if self.check_for_errors {
                    let error = self.session.struct_span_err(
                        self.current_span,
                        "this argument should be a string literal, do not call this function directly",
                    );
                    self.emit_diagnostic(error);
                }
                Rc::new("dummy argument".to_string())
            }
        }
    }

    /// Adds the first and only value in actual_args to the path condition of the destination.
    /// No check is performed, since we get to assume this condition without proof.
    #[logfn_inputs(TRACE)]
    fn handle_assume(&mut self, call_info: &CallInfo<'_, 'tcx>) {
        precondition!(call_info.actual_args.len() == 1);
        let assumed_condition = &call_info.actual_args[0].1;
        let exit_condition = self
            .current_environment
            .entry_condition
            .and(assumed_condition.clone());
        if let Some((_, target)) = &call_info.destination {
            self.current_environment.exit_conditions = self
                .current_environment
                .exit_conditions
                .insert(*target, exit_condition);
        } else {
            assume_unreachable!();
        }
        if let Some(cleanup_target) = call_info.cleanup {
            self.current_environment.exit_conditions = self
                .current_environment
                .exit_conditions
                .insert(cleanup_target, abstract_value::FALSE.into());
        }
    }

    fn handle_post_condition(&mut self, call_info: &CallInfo<'_, 'tcx>) {
        precondition!(call_info.actual_args.len() == 3);
        let condition = call_info.actual_args[0].1.clone();
        let exit_condition = self.current_environment.entry_condition.and(condition);
        if let Some((_, target)) = &call_info.destination {
            self.current_environment.exit_conditions = self
                .current_environment
                .exit_conditions
                .insert(*target, exit_condition);
        } else {
            assume_unreachable!();
        }
    }

    /// It is bad style for a precondition to be reached conditionally, since well, that condition
    /// should be part of the precondition.
    #[logfn_inputs(TRACE)]
    fn handle_precondition_start(&mut self, call_info: &CallInfo<'_, 'tcx>) {
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
        if let Some((_, target)) = &call_info.destination {
            self.current_environment.exit_conditions = self
                .current_environment
                .exit_conditions
                .insert(*target, exit_condition);
        } else {
            assume_unreachable!();
        }
    }

    /// Adds the first and only value in actual_args to the current list of preconditions.
    /// No check is performed, since we get to assume the caller has verified this condition.
    #[logfn_inputs(TRACE)]
    fn handle_precondition(&mut self, call_info: &CallInfo<'_, 'tcx>) {
        precondition!(call_info.actual_args.len() == 2);
        if self.check_for_errors {
            let condition = call_info.actual_args[0].1.clone();
            let message = self.coerce_to_string(&call_info.actual_args[1].1);
            let precondition = Precondition {
                condition,
                message,
                provenance: None,
                spans: vec![self.current_span],
            };
            self.preconditions.push(precondition);
        }
    }

    /// Provides special handling of functions that have no MIR bodies or that need to access
    /// internal MIRAI state in ways that cannot be expressed in normal Rust and therefore
    /// cannot be summarized in the standard_contracts crate.
    /// Returns the result of the call, or BOTTOM if the function to call is not a known
    /// special function.
    #[allow(clippy::cognitive_complexity)]
    #[logfn_inputs(TRACE)]
    fn try_to_inline_special_function(
        &mut self,
        call_info: &CallInfo<'_, 'tcx>,
    ) -> Rc<AbstractValue> {
        match call_info.callee_known_name {
            KnownNames::RustAlloc => self.handle_rust_alloc(call_info),
            KnownNames::RustAllocZeroed => self.handle_rust_alloc_zeroed(call_info),
            KnownNames::RustRealloc => self.handle_rust_realloc(call_info),
            KnownNames::StdIntrinsicsArithOffset => self.handle_arith_offset(call_info),
            KnownNames::StdIntrinsicsBitreverse
            | KnownNames::StdIntrinsicsBswap
            | KnownNames::StdIntrinsicsCtlz
            | KnownNames::StdIntrinsicsCtpop
            | KnownNames::StdIntrinsicsCttz => {
                checked_assume!(call_info.actual_args.len() == 1);
                let arg_type: ExpressionType = (&call_info.actual_argument_types[0].kind).into();
                let bit_length = arg_type.bit_length();
                call_info.actual_args[0]
                    .1
                    .intrinsic_bit_vector_unary(bit_length, call_info.callee_known_name)
            }
            KnownNames::StdIntrinsicsCtlzNonzero | KnownNames::StdIntrinsicsCttzNonzero => {
                checked_assume!(call_info.actual_args.len() == 1);
                if self.check_for_errors {
                    let non_zero = call_info.actual_args[0].1.not_equals(Rc::new(0u128.into()));
                    self.check_condition(&non_zero, Rc::new("argument is zero".to_owned()), false);
                }
                let arg_type: ExpressionType = (&call_info.actual_argument_types[0].kind).into();
                let bit_length = arg_type.bit_length();
                call_info.actual_args[0]
                    .1
                    .intrinsic_bit_vector_unary(bit_length, call_info.callee_known_name)
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
                checked_assume!(call_info.actual_args.len() == 1);
                call_info.actual_args[0]
                    .1
                    .intrinsic_floating_point_unary(call_info.callee_known_name)
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
                checked_assume!(call_info.actual_args.len() == 2);
                call_info.actual_args[0].1.intrinsic_binary(
                    call_info.actual_args[1].1.clone(),
                    call_info.callee_known_name,
                )
            }
            KnownNames::StdIntrinsicsMulWithOverflow => {
                self.handle_checked_binary_operation(call_info)
            }
            KnownNames::StdIntrinsicsOffset => self.handle_offset(call_info),
            KnownNames::StdIntrinsicsTransmute => {
                checked_assume!(call_info.actual_args.len() == 1);
                call_info.actual_args[0].1.clone()
            }
            KnownNames::StdMemSizeOf => self.handle_size_of(call_info),
            _ => abstract_value::BOTTOM.into(),
        }
    }

    /// Returns a new heap memory block with the given byte length.
    #[logfn_inputs(TRACE)]
    fn handle_rust_alloc(&mut self, call_info: &CallInfo<'_, 'tcx>) -> Rc<AbstractValue> {
        checked_assume!(call_info.actual_args.len() == 2);
        let length = call_info.actual_args[0].1.clone();
        let alignment = call_info.actual_args[1].1.clone();
        let heap_path = Path::get_as_path(self.get_new_heap_block(length, alignment, false));
        AbstractValue::make_reference(Rc::new(heap_path))
    }

    /// Returns a new heap memory block with the given byte length and with the zeroed flag set.
    #[logfn_inputs(TRACE)]
    fn handle_rust_alloc_zeroed(&mut self, call_info: &CallInfo<'_, 'tcx>) -> Rc<AbstractValue> {
        checked_assume!(call_info.actual_args.len() == 2);
        let length = call_info.actual_args[0].1.clone();
        let alignment = call_info.actual_args[1].1.clone();
        let heap_path = Path::get_as_path(self.get_new_heap_block(length, alignment, true));
        AbstractValue::make_reference(Rc::new(heap_path))
    }

    /// Removes the heap block and all paths rooted in it from the current environment.
    #[logfn_inputs(TRACE)]
    fn handle_rust_dealloc(&mut self, call_info: &CallInfo<'_, 'tcx>) -> Rc<AbstractValue> {
        checked_assume!(call_info.actual_args.len() == 3);

        // The current environment is that that of the caller, but the caller is a standard
        // library function and has no interesting state to purge.
        // The layout path inserted below will become a side effect of the caller and when that
        // side effect is refined by the caller's caller, the refinement will do the purge if the
        // qualifier of the path is a heap block path.

        // Get path to the heap block to deallocate
        let heap_block_path = call_info.actual_args[0].0.clone();

        // Create a layout
        let length = call_info.actual_args[1].1.clone();
        let alignment = call_info.actual_args[2].1.clone();
        let layout = AbstractValue::make_from(
            Expression::HeapBlockLayout {
                length,
                alignment,
                source: LayoutSource::DeAlloc,
            },
            1,
        );

        // Get a layout path and update the environment
        let layout_path = Path::new_layout(heap_block_path).refine_paths(&self.current_environment);
        self.current_environment
            .update_value_at(layout_path, layout);

        // Signal to the caller that there is no return result
        abstract_value::BOTTOM.into()
    }

    /// Sets the length of the heap block to a new value and removes index paths as necessary
    /// if the new length is known and less than the old lengths.
    #[logfn_inputs(TRACE)]
    fn handle_rust_realloc(&mut self, call_info: &CallInfo<'_, 'tcx>) -> Rc<AbstractValue> {
        checked_assume!(call_info.actual_args.len() == 4);
        // Get path to the heap block to reallocate
        let heap_block_path = Path::new_deref(call_info.actual_args[0].0.clone());

        // Create a layout
        let length = call_info.actual_args[1].1.clone();
        let alignment = call_info.actual_args[2].1.clone();
        let new_length = call_info.actual_args[3].1.clone();
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
        let layout_path = Path::new_layout(heap_block_path).refine_paths(&self.current_environment);
        self.current_environment
            .update_value_at(layout_path.clone(), new_length_layout);
        let layout_path2 = Path::new_layout(layout_path);
        self.current_environment
            .update_value_at(layout_path2, layout_param);

        // Return the original heap block reference as the result
        call_info.actual_args[0].1.clone()
    }

    /// Set the call result to an offset derived from the arguments. Does no checking.
    #[logfn_inputs(TRACE)]
    fn handle_arith_offset(&mut self, call_info: &CallInfo<'_, 'tcx>) -> Rc<AbstractValue> {
        checked_assume!(call_info.actual_args.len() == 2);
        let base_val = &call_info.actual_args[0].1;
        let offset_val = &call_info.actual_args[1].1;
        base_val.offset(offset_val.clone())
    }

    /// Copies a slice of elements from the source to the destination.
    #[logfn_inputs(TRACE)]
    fn handle_copy_non_overlapping(&mut self, call_info: &CallInfo<'_, 'tcx>) {
        checked_assume!(call_info.actual_args.len() == 3);
        let target_root = call_info.actual_args[0].0.clone();
        let source_path = call_info.actual_args[1].0.clone();
        let count = call_info.actual_args[2].1.clone();
        let target_path = Path::new_slice(target_root, count, &self.current_environment);
        let collection_type = call_info.actual_argument_types[0];
        self.copy_or_move_elements(target_path, source_path, collection_type, false);
    }

    /// Update the state to reflect a call to an intrinsic binary operation that returns a tuple
    /// of an operation result, modulo its max value, and a flag that indicates if the max value
    /// was exceeded.
    #[logfn_inputs(TRACE)]
    fn handle_checked_binary_operation(
        &mut self,
        call_info: &CallInfo<'_, 'tcx>,
    ) -> Rc<AbstractValue> {
        checked_assume!(call_info.actual_args.len() == 2);
        if let Some((target_place, _)) = &call_info.destination {
            let bin_op = match call_info.callee_known_name {
                KnownNames::StdIntrinsicsMulWithOverflow => mir::BinOp::Mul,
                _ => assume_unreachable!(),
            };
            let target_path = self.visit_place(target_place);
            let path0 = Path::new_field(target_path.clone(), 0, &self.current_environment);
            let path1 = Path::new_field(target_path.clone(), 1, &self.current_environment);
            let target_type = self.get_target_path_type(&path0);
            let left = call_info.actual_args[0].1.clone();
            let right = call_info.actual_args[1].1.clone();
            let modulo = target_type.modulo_value();
            let (modulo_result, overflow_flag) = if !modulo.is_bottom() {
                let (result, overflow_flag) =
                    Self::do_checked_binary_op(bin_op, target_type.clone(), left, right);
                (result.remainder(target_type.modulo_value()), overflow_flag)
            } else {
                let (result, overflow_flag) =
                    Self::do_checked_binary_op(bin_op, target_type.clone(), left, right);
                // todo: figure out an expression that represents the truncated overflow of a
                // signed operation.
                let unknown_typed_value = AbstractValue::make_from(
                    Expression::Variable {
                        path: path0.clone(),
                        var_type: target_type.clone(),
                    },
                    (path0.path_length() as u64) + 1,
                );
                (
                    overflow_flag.conditional_expression(unknown_typed_value, result),
                    overflow_flag,
                )
            };
            self.current_environment
                .update_value_at(path0, modulo_result);
            self.current_environment
                .update_value_at(path1, overflow_flag);
            AbstractValue::make_from(
                Expression::Variable {
                    path: target_path.clone(),
                    var_type: target_type,
                },
                (target_path.path_length() as u64) + 1,
            )
        } else {
            assume_unreachable!();
        }
    }

    /// Set the call result to an offset derived from the arguments.
    /// Checks that the resulting offset is either in bounds or one
    /// byte past the end of an allocated object.
    #[logfn_inputs(TRACE)]
    fn handle_offset(&mut self, call_info: &CallInfo<'_, 'tcx>) -> Rc<AbstractValue> {
        checked_assume!(call_info.actual_args.len() == 2);
        let base_val = &call_info.actual_args[0].1;
        let offset_val = &call_info.actual_args[1].1;
        let result = base_val.offset(offset_val.clone());
        if self.check_for_errors && self.function_being_analyzed_is_root() {
            self.check_offset(&result)
        }
        result
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
                        .lookup_path_and_refine_result(layout_path, ExpressionType::NonPrimitive)
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
                let warning = self.session.struct_span_warn(span, message);
                self.emit_diagnostic(warning);
            }
        }
    }

    /// Gets the size in bytes of the type parameter T of the std::mem::size_of<T> function.
    /// Returns TOP if T is not a concrete type.
    #[logfn_inputs(TRACE)]
    fn handle_size_of(&mut self, call_info: &CallInfo<'_, 'tcx>) -> Rc<AbstractValue> {
        checked_assume!(call_info.actual_args.is_empty());
        let sym = rustc_span::Symbol::intern("T");
        let t = (call_info.callee_generic_argument_map.as_ref())
            .expect("std::mem::size_of must be called with generic arguments")
            .get(&sym)
            .expect("std::mem::size must have generic argument T");
        let param_env = self.tcx.param_env(call_info.callee_def_id);
        if let Ok(layout) = self.tcx.layout_of(param_env.and(*t)) {
            Rc::new((layout.details.size.bytes() as u128).into())
        } else {
            abstract_value::TOP.into()
        }
    }

    /// Fn::call, FnMut::call_mut, FnOnce::call_once all receive two arguments:
    /// 1. A function pointer or closure instance to call.
    /// 2. A tuple of argument values for the call.
    /// The tuple is unpacked and the callee is then invoked with its normal function signature.
    /// In the case of calling a closure, the closure signature includes the closure as the first argument.
    ///
    /// All of this happens in code that is not encoded as MIR, so MIRAI needs built in support for it.
    #[logfn_inputs(TRACE)]
    fn try_to_inline_indirectly_called_function(
        &mut self,
        caller_call_info: &CallInfo<'_, 'tcx>,
    ) -> Rc<AbstractValue> {
        checked_assume!(caller_call_info.actual_args.len() == 2);
        // Get the function to call (it is either a function pointer or a closure)
        let callee = caller_call_info.actual_args[0].1.clone();

        // Get the path of the tuple containing the arguments.
        let callee_arg_array_path = caller_call_info.actual_args[1].0.clone();

        // Unpack the arguments. We use the generic arguments of the caller as a proxy for the callee function signature.
        let generic_argument_types: Vec<Ty<'tcx>> = caller_call_info
            .callee_generic_arguments
            .expect("call_once, etc. are generic")
            .as_ref()
            .iter()
            .map(|gen_arg| gen_arg.expect_ty())
            .collect();

        checked_assume!(generic_argument_types.len() == 2);
        let actual_argument_types: Vec<Ty<'tcx>>;
        if let TyKind::Tuple(tuple_types) = generic_argument_types[1].kind {
            actual_argument_types = tuple_types
                .iter()
                .map(|gen_arg| gen_arg.expect_ty())
                .collect();
        } else {
            assume_unreachable!("expected second type argument to be a tuple type");
        }

        let mut actual_args: Vec<(Rc<Path>, Rc<AbstractValue>)> = actual_argument_types
            .iter()
            .enumerate()
            .map(|(i, t)| {
                let arg_path =
                    Path::new_field(callee_arg_array_path.clone(), i, &self.current_environment);
                let arg_val =
                    self.lookup_path_and_refine_result(arg_path.clone(), (&t.kind).into());
                (arg_path, arg_val)
            })
            .collect();

        // Prepend the closure (if there is one) to the unpacked arguments vector.
        // Also update the Self parameter in the arguments map.
        let mut call_info = caller_call_info.clone();
        let mut closure_ty = caller_call_info.actual_argument_types[0];
        if let TyKind::Ref(_, ty, _) = closure_ty.kind {
            closure_ty = ty;
        }
        if self.get_def_id_from_closure(closure_ty).is_some() {
            actual_args.insert(0, caller_call_info.actual_args[0].clone());
            if let TyKind::Closure(_, substs) = closure_ty.kind {
                let mut map = call_info
                    .callee_generic_argument_map
                    .unwrap_or_else(HashMap::new);
                if let Some(ty) = substs.types().next() {
                    let self_sym = rustc_span::Symbol::intern("Self");
                    map.insert(self_sym, ty);
                }
                call_info.callee_generic_argument_map = Some(map);
            }
        }

        let function_constant_args = self.get_function_constant_args(&actual_args);
        let callee_func_ref = self.get_func_ref(&callee);
        call_info.callee_func_ref = callee_func_ref;
        call_info.callee_fun_val = callee;
        call_info.callee_known_name = KnownNames::None;
        call_info.actual_args = &actual_args;
        call_info.actual_argument_types = &actual_argument_types;
        call_info.function_constant_args = &function_constant_args;
        let function_summary = if let Some(func_ref) = &call_info.callee_func_ref {
            call_info.callee_def_id = func_ref.def_id.expect("defined when used here");
            let summary = self.get_function_summary(&call_info);
            if let Some(summary) = summary {
                summary
            } else {
                self.deal_with_missing_summary(&call_info);
                Summary::default()
            }
        } else {
            self.deal_with_missing_summary(&call_info);
            Summary::default()
        };

        self.check_preconditions_if_necessary(&call_info, &function_summary);
        self.transfer_and_refine_normal_return_state(&call_info, &function_summary);
        self.transfer_and_refine_cleanup_state(&call_info, &function_summary);
        abstract_value::TOP.into()
    }

    /// Checks if the preconditions obtained from the summary of the function being called
    /// are met by the current state and arguments of the calling function.
    /// Preconditions that are definitely false and reachable cause diagnostic messages.
    /// Preconditions that are maybe false become preconditions of the calling function
    /// unless the calling function is an analysis root, in which case a diagnostic message is issued.
    #[logfn_inputs(TRACE)]
    fn check_function_preconditions(
        &mut self,
        call_info: &CallInfo<'_, 'tcx>,
        function_summary: &Summary,
    ) {
        verify!(self.check_for_errors);
        for precondition in &function_summary.preconditions {
            let mut refined_condition = precondition
                .condition
                .refine_parameters(call_info.actual_args, self.fresh_variable_offset)
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

            let warn;
            if !refined_precondition_as_bool.unwrap_or(true) {
                // The precondition is definitely false.
                if entry_cond_as_bool.unwrap_or(false) {
                    // We always get to this call
                    self.issue_diagnostic_for_call(call_info, precondition, false);
                    return;
                } else {
                    // Promote the precondition, but be assertive.
                    // When the caller fails to meet the precondition, failure is certain.
                    warn = false;
                }
            } else {
                warn = true;
            }

            // If the current function is not an analysis root, promote the precondition, subject to a k-limit.
            if !self.function_being_analyzed_is_root()
                && self.preconditions.len() < k_limits::MAX_INFERRED_PRECONDITIONS
            {
                // Promote the callee precondition to a precondition of the current function.
                // Unless, of course, if the precondition is already a precondition of the
                // current function.
                let seen_precondition = self.preconditions.iter().any(|pc| {
                    pc.spans.last() == precondition.spans.last()
                        || pc.provenance == precondition.provenance
                });
                if seen_precondition {
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
                return;
            }

            // The precondition cannot be promoted, so the buck stops here.
            self.issue_diagnostic_for_call(call_info, precondition, warn);
        }
    }

    // Issue a diagnostic, but only if there isn't already a diagnostic for this
    // function call.
    #[logfn_inputs(TRACE)]
    fn issue_diagnostic_for_call(
        &mut self,
        call_info: &CallInfo<'_, 'tcx>,
        precondition: &Precondition,
        warn: bool,
    ) {
        if self.check_for_errors
            && !self
                .already_reported_errors_for_call_to
                .contains(&call_info.callee_fun_val)
        {
            self.emit_diagnostic_for_precondition(precondition, warn);
            self.already_reported_errors_for_call_to
                .insert(call_info.callee_fun_val.clone());
        }
    }

    /// Emit a diagnostic to the effect that the current call might violate a the given precondition
    /// of the called function. Use the provenance and spans of the precondition to point out related locations.
    #[logfn_inputs(TRACE)]
    fn emit_diagnostic_for_precondition(&mut self, precondition: &Precondition, warn: bool) {
        precondition!(self.check_for_errors);
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
        let span = self.current_span;
        let mut err = self.session.struct_span_warn(span, diagnostic.as_str());
        for pc_span in precondition.spans.iter() {
            let span_str = self.tcx.sess.source_map().span_to_string(*pc_span);
            if span_str.starts_with("/rustc/") {
                err.span_note(pc_span.clone(), &format!("related location {}", span_str));
            } else {
                err.span_note(pc_span.clone(), "related location");
            };
        }
        self.emit_diagnostic(err);
    }

    /// Updates the current state to reflect the effects of a normal return from the function call.
    #[logfn_inputs(TRACE)]
    fn transfer_and_refine_normal_return_state(
        &mut self,
        call_info: &CallInfo<'_, 'tcx>,
        function_summary: &Summary,
    ) {
        if let Some((place, target)) = &call_info.destination {
            // Assign function result to place
            let target_path = self.visit_place(place);
            let return_value_path = Path::new_result();

            // Transfer side effects
            if function_summary.is_not_default {
                // Effects on the heap
                for (path, value) in function_summary.side_effects.iter() {
                    if path.is_rooted_by_abstract_heap_block() {
                        let rvalue = value
                            .clone()
                            .refine_parameters(call_info.actual_args, self.fresh_variable_offset)
                            .refine_paths(&self.current_environment);
                        self.current_environment
                            .update_value_at(path.clone(), rvalue);
                    }
                }

                // Effects on the call result
                self.transfer_and_refine(
                    &function_summary.side_effects,
                    target_path.clone(),
                    &return_value_path,
                    call_info.actual_args,
                );

                // Effects on the call arguments
                for (i, (target_path, _)) in call_info.actual_args.iter().enumerate() {
                    let parameter_path = Path::new_parameter(i + 1);
                    self.transfer_and_refine(
                        &function_summary.side_effects,
                        target_path.clone(),
                        &parameter_path,
                        call_info.actual_args,
                    );
                }
            } else {
                // We don't know anything other than the return value type.
                // We'll assume there were no side effects and no preconditions (but check this later if possible).
                let result_type = self.get_place_type(place);
                let result = AbstractValue::make_from(
                    Expression::UninterpretedCall {
                        callee: call_info.callee_fun_val.clone(),
                        arguments: call_info
                            .actual_args
                            .iter()
                            .map(|(_, arg)| arg.clone())
                            .collect(),
                        result_type,
                        path: return_value_path.clone(),
                    },
                    1,
                );
                self.current_environment
                    .update_value_at(return_value_path, result);
            }

            // Add post conditions to entry condition
            let mut exit_condition = self.current_environment.entry_condition.clone();
            if let Some(unwind_condition) = &function_summary.unwind_condition {
                exit_condition = exit_condition.and(unwind_condition.logical_not());
            }
            if let Some(post_condition) = &function_summary.post_condition {
                let mut return_value_env = Environment::default();
                let var_type = self.get_place_type(place);
                let result_val = AbstractValue::make_from(
                    Expression::Variable {
                        path: target_path,
                        var_type,
                    },
                    1,
                );
                let return_value_path = Path::new_local(self.fresh_variable_offset);

                return_value_env.update_value_at(return_value_path, result_val);
                let refined_post_condition = post_condition
                    .refine_parameters(call_info.actual_args, self.fresh_variable_offset)
                    .refine_paths(&return_value_env);
                debug!(
                    "refined post condition before path refinement {:?}",
                    refined_post_condition
                );
                let refined_post_condition =
                    refined_post_condition.refine_paths(&self.current_environment);
                debug!("refined post condition {:?}", refined_post_condition);
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
        call_info: &CallInfo<'_, 'tcx>,
        function_summary: &Summary,
    ) {
        if let Some(cleanup_target) = call_info.cleanup {
            for (i, (target_path, _)) in call_info.actual_args.iter().enumerate() {
                let parameter_path = Path::new_parameter(i + 1);
                self.transfer_and_refine(
                    &function_summary.unwind_side_effects,
                    target_path.clone(),
                    &parameter_path,
                    call_info.actual_args,
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
    fn report_calls_to_special_functions(&mut self, call_info: &CallInfo<'_, 'tcx>) {
        precondition!(self.check_for_errors);
        match call_info.callee_known_name {
            KnownNames::MiraiAssume => {
                assume!(call_info.actual_args.len() == 1);
                let (_, cond) = &call_info.actual_args[0];
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
            KnownNames::MiraiPostcondition => {
                assume!(call_info.actual_args.len() == 3); // The type checker ensures this.
                let (_, assumption) = &call_info.actual_args[1];
                let (_, cond) = &call_info.actual_args[0];
                if !assumption.as_bool_if_known().unwrap_or(false) {
                    let message = self.coerce_to_string(&call_info.actual_args[2].1);
                    if self.check_condition(cond, message, true).is_none() {
                        self.try_extend_post_condition(&cond);
                    }
                } else {
                    self.try_extend_post_condition(&cond);
                }
            }
            KnownNames::MiraiVerify => {
                assume!(call_info.actual_args.len() == 2); // The type checker ensures this.
                let (_, cond) = &call_info.actual_args[0];
                let message = self.coerce_to_string(&call_info.actual_args[1].1);
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
            KnownNames::StdPanickingBeginPanic | KnownNames::StdPanickingBeginPanicFmt => {
                assume!(!call_info.actual_args.is_empty()); // The type checker ensures this.
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
                    call_info.actual_args[0].1.expression
                {
                    if msg.contains("entered unreachable code")
                        || msg.contains("not yet implemented")
                    {
                        // We treat unreachable!() as an assumption rather than an assertion to prove.
                        // unimplemented!() is unlikely to be a programmer mistake, so need to fixate on that either.
                        return;
                    } else {
                        if path_cond.is_none() && msg.as_str() == "statement is reachable" {
                            // verify_unreachable should always complain if possibly reachable
                            // and the current function is public or root.
                            path_cond = Some(true);
                        }
                        msg.clone()
                    }
                } else {
                    Rc::new(String::from("execution panic"))
                };
                let span = self.current_span;

                if path_cond.unwrap_or(false) && self.function_being_analyzed_is_root() {
                    // We always get to this call and we have to assume that the function will
                    // get called, so keep the message certain.
                    // Don't, however, complain about panics in the standard contract summaries
                    if std::env::var("MIRAI_START_FRESH").is_err() {
                        let err = self.session.struct_span_warn(span, msg.as_str());
                        self.emit_diagnostic(err);
                    }
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
                    let precondition = Precondition {
                        condition,
                        message: msg,
                        provenance: None,
                        spans: if self.def_id.is_local() {
                            vec![span]
                        } else {
                            vec![] // The span is likely inside a standard macro
                        },
                    };
                    self.preconditions.push(precondition);
                }
            }
            _ => assume_unreachable!(),
        }
    }

    /// Extend the current post condition by the given `cond`. If none was set before,
    /// this will just set it for the first time. If there is already a post condition.
    /// we check whether it is safe to extend it. It is considered safe if the block where
    /// it was set dominates the existing one.
    #[logfn_inputs(TRACE)]
    fn try_extend_post_condition(&mut self, cond: &Rc<AbstractValue>) {
        precondition!(self.check_for_errors);
        let this_block = self.current_location.block;
        match (self.post_condition.clone(), self.post_condition_block) {
            (Some(last_cond), Some(last_block)) => {
                let dominators = self.mir.dominators();
                if dominators.is_dominated_by(this_block, last_block) {
                    // We can extend the last condition as all paths to this condition
                    // lead over it
                    self.post_condition = Some(last_cond.and(cond.clone()));
                    self.post_condition_block = Some(this_block);
                } else {
                    let span = self.current_span;
                    let warning = self.session.struct_span_warn(
                        span,
                        "multiple post conditions must be on the same execution path",
                    );
                    self.emit_diagnostic(warning);
                }
            }
            (_, _) => {
                self.post_condition = Some(cond.clone());
                self.post_condition_block = Some(this_block);
            }
        }
    }

    /// Check if the given condition is reachable and true.
    /// If not issue a warning if the function is public and return the warning message, if
    /// the condition is not a post condition.
    #[logfn_inputs(TRACE)]
    fn check_condition(
        &mut self,
        cond: &Rc<AbstractValue>,
        message: Rc<String>,
        is_post_condition: bool,
    ) -> Option<String> {
        precondition!(self.check_for_errors);
        let (cond_as_bool, entry_cond_as_bool) = self.check_condition_value_and_reachability(cond);

        // If we never get here, rather call unreachable!()
        if !entry_cond_as_bool.unwrap_or(true) {
            let span = self.current_span;
            let message =
                "this is unreachable, mark it as such by using the verify_unreachable! macro";
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
            if !is_post_condition
                && entry_cond_as_bool.is_none()
                && self.preconditions.len() < k_limits::MAX_INFERRED_PRECONDITIONS
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
        if self.function_being_analyzed_is_root()
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

    /// Returns true if the function being analyzed is an analysis root.
    #[logfn_inputs(TRACE)]
    fn function_being_analyzed_is_root(&mut self) -> bool {
        self.active_calls.len() <= 1
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
                            let source_path = Rc::new(Path::get_as_path(rvalue.clone()));
                            let target_type =
                                Self::get_element_type(self.get_path_rustc_type(&target_path));
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
                Expression::Variable { path, .. } => {
                    let target_type = self.get_path_rustc_type(&tpath);
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
                    ExpressionType::NonPrimitive,
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
                    ExpressionType::NonPrimitive,
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
                                            let new_block_path =
                                                Rc::new(Path::get_as_path(new_block));
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
                let error = self.session.struct_span_err(
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
                let error = self.session.struct_span_err(self.current_span, &message);
                self.emit_diagnostic(error);
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
            let panic_exit_condition = self.current_environment.entry_condition.and(if expected {
                not_cond_val.clone()
            } else {
                cond_val.clone()
            });
            self.current_environment.exit_conditions = self
                .current_environment
                .exit_conditions
                .insert(cleanup_target, panic_exit_condition);
        };
        let normal_exit_condition = self.current_environment.entry_condition.and(if expected {
            cond_val.clone()
        } else {
            not_cond_val
        });
        self.current_environment.exit_conditions = self
            .current_environment
            .exit_conditions
            .insert(target, normal_exit_condition);

        // Check the condition and issue a warning or infer a precondition.
        if self.check_for_errors {
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
                        let span = self.current_span;
                        let error = self.session.struct_span_warn(span, error);
                        self.emit_diagnostic(error);
                        // No need to push a precondition, the caller can never satisfy it.
                        return;
                    }
                }

                // At this point, we don't know that this assert is unreachable and we don't know
                // that the condition is as expected, so we need to warn about it somewhere.
                if self.function_being_analyzed_is_root()
                    || self.preconditions.len() >= k_limits::MAX_INFERRED_PRECONDITIONS
                {
                    // Can't make this the caller's problem.
                    let warning = format!("possible {}", get_assert_msg_description(msg));
                    let span = self.current_span;
                    let warning = self.session.struct_span_warn(span, warning.as_str());
                    self.emit_diagnostic(warning);
                    return;
                }

                // Make it the caller's problem by pushing a precondition.
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
                    let message = Rc::new(String::from(get_assert_msg_description(msg)));
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
            mir::Rvalue::Ref(_, _, place) | mir::Rvalue::AddressOf(_, place) => {
                self.visit_address_of(path, place);
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
                    user_ty, literal, ..
                } = constant.borrow();
                let target_type = literal.ty;
                let const_value = self.visit_constant(*user_ty, &literal);
                match &const_value.expression {
                    Expression::HeapBlock { .. } => {
                        let rpath = Rc::new(
                            PathEnum::HeapBlock {
                                value: const_value.clone(),
                            }
                            .into(),
                        );
                        self.copy_or_move_elements(path, rpath, target_type, false);
                    }
                    _ => {
                        let rpath = Path::new_constant(const_value.clone());
                        self.copy_or_move_elements(path, rpath, target_type, false);
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
        let rtype = self.get_rustc_place_type(place);
        self.copy_or_move_elements(target_path, rpath, rtype, false);
    }

    /// Copies/moves all paths rooted in rpath to corresponding paths rooted in target_path.
    #[logfn_inputs(TRACE)]
    fn copy_or_move_elements(
        &mut self,
        target_path: Rc<Path>,
        source_path: Rc<Path>,
        target_type: Ty<'tcx>,
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
                    let index_val =
                        Rc::new(self.constant_value_cache.get_u128_for(index).clone().into());
                    let index_path =
                        Path::new_index(qualifier.clone(), index_val, &self.current_environment);
                    self.copy_or_move_elements(target_path, index_path, target_type, move_elements);
                    return;
                }
                PathSelector::ConstantSlice { from, to, from_end } => {
                    self.copy_or_move_subslice(
                        target_path,
                        target_type,
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
                            target_type,
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
        let target_type: ExpressionType = (&target_type.kind).into();
        let value = self.lookup_path_and_refine_result(source_path.clone(), target_type.clone());
        let val_type = value.expression.infer_type();
        let mut no_children = true;
        if val_type == ExpressionType::NonPrimitive {
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
                    debug!("moving {:?} to {:?}", value, qualified_path);
                    value_map = value_map.remove(path);
                } else {
                    debug!("copying {:?} to {:?}", value, qualified_path);
                };
                value_map = value_map.insert(qualified_path, value.clone());
                no_children = false;
            }
        }
        if target_type != ExpressionType::NonPrimitive || no_children {
            let value =
                self.lookup_path_and_refine_result(source_path.clone(), target_type.clone());
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
        let elem_size = self.get_elem_type_size(target_type);
        let byte_len_const = self
            .constant_value_cache
            .get_u128_for(u128::from((to - from) as u64 * elem_size))
            .clone();
        let length = Rc::new(byte_len_const.into());
        let alignment = Rc::new(1u128.into());
        let slice_value = self.get_new_heap_block(length, alignment, false);
        self.current_environment
            .update_value_at(target_path.clone(), slice_value.clone());
        let slice_path = Rc::new(PathEnum::HeapBlock { value: slice_value }.into());
        let slice_len_path = Path::new_length(slice_path, &self.current_environment);
        let len_const = self
            .constant_value_cache
            .get_u128_for(u128::from(to - from))
            .clone();
        let len_value: Rc<AbstractValue> = Rc::new(len_const.into());
        self.current_environment
            .update_value_at(slice_len_path, len_value);
        for i in from..to {
            let index_val = Rc::new(
                self.constant_value_cache
                    .get_u128_for(u128::from(i))
                    .clone()
                    .into(),
            );
            let index_path =
                Path::new_index(qualifier.clone(), index_val, &self.current_environment);
            let target_index_val = Rc::new(
                self.constant_value_cache
                    .get_u128_for(u128::try_from(i - from).unwrap())
                    .clone()
                    .into(),
            );
            let indexed_target = Path::new_index(
                target_path.clone(),
                target_index_val,
                &self.current_environment,
            );
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
                let additional_value = self.lookup_path_and_refine_result(
                    source_path_with_selectors,
                    value.expression.infer_type(),
                );
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
    fn expand_aliased_string_literals(
        &mut self,
        target_path: &Rc<Path>,
        rtype: ExpressionType,
        mut value_map: HashTrieMap<Rc<Path>, Rc<AbstractValue>>,
        value: &Rc<AbstractValue>,
    ) -> HashTrieMap<Rc<Path>, Rc<AbstractValue>> {
        if rtype == ExpressionType::Reference {
            if let Expression::CompileTimeConstant(ConstantDomain::Str(s)) = &value.expression {
                if let PathEnum::LocalVariable { .. } = &target_path.value {
                    let lh_type = self.get_path_rustc_type(&target_path);
                    if let TyKind::Ref(_, ty, _) = lh_type.kind {
                        if let TyKind::Slice(elem_ty) = ty.kind {
                            if let TyKind::Uint(syntax::ast::UintTy::U8) = elem_ty.kind {
                                let collection_path = Path::new_constant(value.clone());
                                for (i, ch) in s.as_bytes().iter().enumerate() {
                                    let index = Rc::new((i as u128).into());
                                    let ch_const = Rc::new((*ch as u128).into());
                                    let path = Path::new_index(
                                        collection_path.clone(),
                                        index,
                                        &self.current_environment,
                                    );
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

    /// For each (path', value) pair in the environment where path' is rooted in place,
    /// add a (path'', value) pair to the environment where path'' is a copy of path re-rooted
    /// with place, and also remove the (path', value) pair from the environment.
    #[logfn_inputs(TRACE)]
    fn visit_used_move(&mut self, target_path: Rc<Path>, place: &mir::Place<'tcx>) {
        let rpath = self.visit_place(place);
        let rtype = self.get_rustc_place_type(place);
        self.copy_or_move_elements(target_path, rpath, rtype, true);
    }

    /// path = [x; 32]
    #[logfn_inputs(TRACE)]
    fn visit_repeat(&mut self, path: Rc<Path>, operand: &mir::Operand<'tcx>, count: u64) {
        let length_path = Path::new_length(path.clone(), &self.current_environment);
        let length_value: Rc<AbstractValue> = Rc::new(
            self.constant_value_cache
                .get_u128_for(u128::from(count))
                .clone()
                .into(),
        );
        self.current_environment
            .update_value_at(length_path, length_value.clone());
        let slice_path = Path::new_slice(path, length_value, &self.current_environment);
        let initial_value = self.visit_operand(operand);
        self.current_environment
            .update_value_at(slice_path, initial_value);
    }

    /// path = &x or &mut x or &raw const x
    #[logfn_inputs(TRACE)]
    fn visit_address_of(&mut self, path: Rc<Path>, place: &mir::Place<'tcx>) {
        let target_type = self.get_rustc_place_type(place);
        let value_path = self
            .visit_place(place)
            .refine_paths(&self.current_environment);
        let value = match &value_path.value {
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } if *selector.as_ref() == PathSelector::Deref => {
                // We are taking a reference to the result of a deref. This is a bit awkward.
                // The deref essentially does a copy of the value denoted by the qualifier.
                // If this value is structured and not heap allocated, the copy must be done
                // with copy_or_move_elements.
                self.copy_or_move_elements(path, qualifier.clone(), target_type, false);
                return;
            }
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                // We are taking a reference to a path that may be rooted in a local that
                // itself contains a reference. We'd like to eliminate that local to keep
                // paths canonical and to avoid leaking locals into summaries.
                let refined_qualifier = qualifier.refine_paths(&self.current_environment);
                if refined_qualifier != *qualifier {
                    let refined_path = Path::new_qualified(refined_qualifier, selector.clone());
                    AbstractValue::make_reference(refined_path)
                } else {
                    AbstractValue::make_reference(value_path)
                }
            }
            PathEnum::PromotedConstant { .. } => {
                if let Some(val) = self.current_environment.value_at(&value_path) {
                    if let Expression::HeapBlock { .. } = &val.expression {
                        let heap_path = Rc::new(PathEnum::HeapBlock { value: val.clone() }.into());
                        AbstractValue::make_reference(heap_path)
                    } else {
                        AbstractValue::make_reference(value_path)
                    }
                } else {
                    AbstractValue::make_reference(value_path)
                }
            }
            PathEnum::HeapBlock { value } => value.clone(),
            _ => AbstractValue::make_reference(value_path),
        };
        self.current_environment.update_value_at(path, value);
    }

    /// path = length of a [X] or [X;n] value.
    #[logfn_inputs(TRACE)]
    fn visit_len(&mut self, path: Rc<Path>, place: &mir::Place<'tcx>) {
        let place_ty = self.get_rustc_place_type(place);
        let len_value = if let TyKind::Array(_, len) = &place_ty.kind {
            // We only get here if "-Z mir-opt-level=0" was specified.
            // With more optimization the len instruction becomes a constant.
            self.visit_constant(None, &len)
        } else {
            let value_path = self.visit_place(place);
            self.get_len(value_path)
        };
        self.current_environment.update_value_at(path, len_value);
    }

    /// Get the length of an array. Will be a compile time constant if the array length is known.
    #[logfn_inputs(TRACE)]
    fn get_len(&mut self, path: Rc<Path>) -> Rc<AbstractValue> {
        let length_path = Path::new_length(path, &self.current_environment);
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
            operand.cast(ExpressionType::from(&ty.kind))
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
        let (result, overflow_flag) = Self::do_checked_binary_op(bin_op, target_type, left, right);
        let path0 = Path::new_field(path.clone(), 0, &self.current_environment);
        self.current_environment.update_value_at(path0, result);
        let path1 = Path::new_field(path, 1, &self.current_environment);
        self.current_environment
            .update_value_at(path1, overflow_flag);
    }

    /// Apply the given binary operator to the two operands, with overflow checking where appropriate
    #[logfn_inputs(TRACE)]
    fn do_checked_binary_op(
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
    fn visit_nullary_op(&mut self, path: Rc<Path>, null_op: mir::NullOp, ty: rustc::ty::Ty<'tcx>) {
        let param_env = self.tcx.param_env(self.def_id);
        let len = if let Ok(layout) = self.tcx.layout_of(param_env.and(ty)) {
            Rc::new((layout.details.size.bytes() as u128).into())
        } else {
            abstract_value::TOP.into()
        };
        let alignment = Rc::new(1u128.into());
        let value = match null_op {
            mir::NullOp::Box => self.get_new_heap_block(len, alignment, false),
            mir::NullOp::SizeOf => len,
        };
        self.current_environment.update_value_at(path, value);
    }

    /// Allocates a new heap block and caches it, keyed with the current location
    /// so that subsequent visits deterministically use the same heap block when processing
    /// the instruction at this location. If we don't do this the fixed point loop wont converge.
    /// Note, however, that this is not good enough for the outer fixed point because the counter
    /// is shared between different functions unless it is reset to 0 for each function.
    #[logfn_inputs(TRACE)]
    fn get_new_heap_block(
        &mut self,
        length: Rc<AbstractValue>,
        alignment: Rc<AbstractValue>,
        is_zeroed: bool,
    ) -> Rc<AbstractValue> {
        let addresses = &mut self.heap_addresses;
        let constants = &mut self.constant_value_cache;
        let block = addresses
            .entry(self.current_location)
            .or_insert_with(|| AbstractValue::make_from(constants.get_new_heap_block(is_zeroed), 1))
            .clone();
        let block_path = Rc::new(Path::get_as_path(block.clone()));
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
        let discriminant_path =
            Path::new_discriminant(self.visit_place(place), &self.current_environment);
        let discriminant_type = ExpressionType::U128;
        let discriminant_value =
            self.lookup_path_and_refine_result(discriminant_path, discriminant_type);
        self.current_environment
            .update_value_at(path, discriminant_value);
    }

    /// Returns the size in bytes (including padding) or an element of the given collection type.
    /// If the type is not a collection, it returns one.
    fn get_elem_type_size(&self, ty: Ty<'tcx>) -> u64 {
        match ty.kind {
            TyKind::Array(ty, _) | TyKind::Slice(ty) => self.get_type_size(ty),
            TyKind::RawPtr(t) => self.get_type_size(t.ty),
            _ => 1,
        }
    }

    /// Returns the size in bytes (including padding) of an instance of the given type.
    fn get_type_size(&self, ty: Ty<'tcx>) -> u64 {
        let param_env = self.tcx.param_env(self.def_id);
        if let Ok(layout) = self.tcx.layout_of(param_env.and(ty)) {
            layout.details.size.bytes()
        } else {
            0
        }
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
        precondition!(matches!(aggregate_kinds, mir::AggregateKind::Array(..)));
        if path.path_length() >= k_limits::MAX_PATH_LENGTH {
            // If we get to this limit we have a very weird array. Just use Top.
            self.current_environment
                .update_value_at(path, abstract_value::TOP.into());
            return;
        }
        let length_path = Path::new_length(path.clone(), &self.current_environment);
        let length_value: Rc<AbstractValue> = Rc::new(
            self.constant_value_cache
                .get_u128_for(operands.len() as u128)
                .clone()
                .into(),
        );

        let elem_size = match *aggregate_kinds {
            mir::AggregateKind::Array(ty) => self.get_type_size(ty),
            _ => verify_unreachable!(),
        };
        let byte_size = (operands.len() as u64) * elem_size.max(1);
        let byte_size_value: Rc<AbstractValue> = Rc::new(
            self.constant_value_cache
                .get_u128_for(byte_size as u128)
                .clone()
                .into(),
        );
        let alignment: Rc<AbstractValue> = Rc::new(
            (match elem_size {
                0 => 1,
                1 | 2 | 4 | 8 => elem_size,
                _ => 8,
            } as u128)
                .into(),
        );
        let aggregate_value = self.get_new_heap_block(byte_size_value, alignment, false);
        self.current_environment
            .update_value_at(path.clone(), aggregate_value);

        // remove the length path from current environment if present (it is no longer canonical).
        self.current_environment.value_map =
            self.current_environment.value_map.remove(&length_path);

        // Re-canonicalize length_path
        let length_path = length_path.refine_paths(&self.current_environment);

        for (i, operand) in operands.iter().enumerate() {
            let index_value = Rc::new(
                self.constant_value_cache
                    .get_u128_for(i as u128)
                    .clone()
                    .into(),
            );
            let index_path = Path::new_index(path.clone(), index_value, &self.current_environment);
            self.visit_used_operand(index_path, operand);
        }
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
                    user_ty, literal, ..
                } = constant.borrow();
                let const_value = self.visit_constant(*user_ty, &literal);
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
            mir::Operand::Constant(..) => Path::new_constant(self.visit_operand(operand)),
        }
    }

    /// Returns the rustc Ty of the given operand.
    #[logfn_inputs(TRACE)]
    fn get_operand_rustc_type(&mut self, operand: &mir::Operand<'tcx>) -> Ty<'tcx> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                self.get_rustc_place_type(place)
            }
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

    /// If Operand corresponds to a compile time constant function, return
    /// the generic parameter substitutions (type arguments) that are used by
    /// the call instruction whose operand this is.
    #[logfn_inputs(TRACE)]
    fn get_generic_arguments_map(
        &self,
        def_id: DefId,
        generic_args: SubstsRef<'tcx>,
        actual_argument_types: &[Ty<'tcx>],
    ) -> Option<HashMap<rustc_span::Symbol, Ty<'tcx>>> {
        if generic_args.is_empty() {
            return None;
        }
        let mut substitution_map = self.generic_argument_map.clone();
        let mut map: HashMap<rustc_span::Symbol, Ty<'tcx>> = HashMap::new();

        // This iterates over the callee's generic parameter definitions.
        // If the parent of the callee is generic, those definitions are iterated
        // as well. This applies recursively. Note that a child cannot mask the
        // generic parameters of its parent with one of its own, so each parameter
        // definition in this iteration will have a unique name.
        InternalSubsts::for_item(self.tcx, def_id, |param_def, _| {
            if let Some(gen_arg) = generic_args.get(param_def.index as usize) {
                if let GenericArgKind::Type(ty) = gen_arg.unpack() {
                    let specialized_gen_arg_ty =
                        self.specialize_generic_argument_type(ty, &substitution_map);
                    if let Some(substitution_map) = &mut substitution_map {
                        substitution_map.insert(param_def.name, specialized_gen_arg_ty);
                    }
                    map.insert(param_def.name, specialized_gen_arg_ty);
                }
            } else {
                debug!("unmapped generic param def");
            }
            self.tcx.mk_param_from_def(param_def) // not used
        });
        // Add "Self" -> actual_argument_types[0]
        if let Some(self_ty) = actual_argument_types.get(0) {
            let self_ty = if let TyKind::Ref(_, ty, _) = self_ty.kind {
                ty
            } else {
                self_ty
            };
            let self_sym = rustc_span::Symbol::intern("Self");
            map.entry(self_sym).or_insert(self_ty);
        }
        Some(map)
    }

    #[logfn_inputs(TRACE)]
    fn specialize_generic_argument(
        &self,
        gen_arg: GenericArg<'tcx>,
        map: &Option<HashMap<rustc_span::Symbol, Ty<'tcx>>>,
    ) -> GenericArg<'tcx> {
        match gen_arg.unpack() {
            GenericArgKind::Type(ty) => self.specialize_generic_argument_type(ty, map).into(),
            _ => gen_arg,
        }
    }

    #[logfn_inputs(TRACE)]
    fn specialize_substs(
        &self,
        substs: SubstsRef<'tcx>,
        map: &Option<HashMap<rustc_span::Symbol, Ty<'tcx>>>,
    ) -> SubstsRef<'tcx> {
        let specialized_generic_args: Vec<GenericArg<'_>> = substs
            .iter()
            .map(|gen_arg| self.specialize_generic_argument(*gen_arg, &map))
            .collect();
        self.tcx.intern_substs(&specialized_generic_args)
    }

    #[logfn_inputs(TRACE)]
    fn specialize_generic_argument_type(
        &self,
        gen_arg_type: Ty<'tcx>,
        map: &Option<HashMap<rustc_span::Symbol, Ty<'tcx>>>,
    ) -> Ty<'tcx> {
        if map.is_none() {
            return gen_arg_type;
        }
        match gen_arg_type.kind {
            TyKind::Adt(def, substs) => self.tcx.mk_adt(def, self.specialize_substs(substs, map)),
            TyKind::Array(elem_ty, _) => {
                let specialized_elem_ty = self.specialize_generic_argument_type(elem_ty, map);
                self.tcx.mk_array(specialized_elem_ty, 1) //todo: use the actual value
            }
            TyKind::Slice(elem_ty) => {
                let specialized_elem_ty = self.specialize_generic_argument_type(elem_ty, map);
                self.tcx.mk_slice(specialized_elem_ty)
            }
            TyKind::RawPtr(rustc::ty::TypeAndMut { ty, mutbl }) => {
                let specialized_ty = self.specialize_generic_argument_type(ty, map);
                self.tcx.mk_ptr(rustc::ty::TypeAndMut {
                    ty: specialized_ty,
                    mutbl,
                })
            }
            TyKind::Ref(region, ty, mutbl) => {
                let specialized_ty = self.specialize_generic_argument_type(ty, map);
                self.tcx.mk_ref(
                    region,
                    rustc::ty::TypeAndMut {
                        ty: specialized_ty,
                        mutbl,
                    },
                )
            }
            TyKind::FnDef(def_id, substs) => self
                .tcx
                .mk_fn_def(def_id, self.specialize_substs(substs, map)),
            TyKind::FnPtr(fn_sig) => {
                let map_fn_sig = |fn_sig: FnSig<'tcx>| {
                    let specialized_inputs_and_output = self.tcx.mk_type_list(
                        fn_sig
                            .inputs_and_output
                            .iter()
                            .map(|ty| self.specialize_generic_argument_type(ty, map)),
                    );
                    FnSig {
                        inputs_and_output: specialized_inputs_and_output,
                        c_variadic: fn_sig.c_variadic,
                        unsafety: fn_sig.unsafety,
                        abi: fn_sig.abi,
                    }
                };
                let specialized_fn_sig = fn_sig.map_bound(map_fn_sig);
                self.tcx.mk_fn_ptr(specialized_fn_sig)
            }
            TyKind::Dynamic(predicates, region) => {
                let map_predicates = |predicates: &rustc::ty::List<ExistentialPredicate<'tcx>>| {
                    self.tcx.mk_existential_predicates(predicates.iter().map(
                        |pred: &ExistentialPredicate<'tcx>| match pred {
                            ExistentialPredicate::Trait(ExistentialTraitRef { def_id, substs }) => {
                                ExistentialPredicate::Trait(ExistentialTraitRef {
                                    def_id: *def_id,
                                    substs: self.specialize_substs(substs, map),
                                })
                            }
                            ExistentialPredicate::Projection(ExistentialProjection {
                                item_def_id,
                                substs,
                                ty,
                            }) => ExistentialPredicate::Projection(ExistentialProjection {
                                item_def_id: *item_def_id,
                                substs: self.specialize_substs(substs, map),
                                ty: self.specialize_generic_argument_type(ty, map),
                            }),
                            ExistentialPredicate::AutoTrait(_) => *pred,
                        },
                    ))
                };
                let specialized_predicates = predicates.map_bound(map_predicates);
                self.tcx.mk_dynamic(specialized_predicates, region)
            }
            TyKind::Closure(def_id, substs) => self
                .tcx
                .mk_closure(def_id, self.specialize_substs(substs, map)),
            TyKind::Generator(def_id, substs, movability) => {
                self.tcx
                    .mk_generator(def_id, self.specialize_substs(substs, map), movability)
            }
            TyKind::GeneratorWitness(bound_types) => {
                let map_types = |types: &rustc::ty::List<Ty<'tcx>>| {
                    self.tcx.mk_type_list(
                        types
                            .iter()
                            .map(|ty| self.specialize_generic_argument_type(ty, map)),
                    )
                };
                let specialized_types = bound_types.map_bound(map_types);
                self.tcx.mk_generator_witness(specialized_types)
            }
            TyKind::Tuple(substs) => self.tcx.mk_tup(
                self.specialize_substs(substs, map)
                    .iter()
                    .map(|gen_arg| gen_arg.expect_ty()),
            ),
            // The projection of an associated type. For example,
            // `<T as Trait<..>>::N`.
            TyKind::Projection(projection) => {
                let specialized_substs = self.specialize_substs(projection.substs, map);
                let item_def_id = projection.item_def_id;
                if utils::are_concrete(specialized_substs) {
                    let param_env = self
                        .tcx
                        .param_env(self.tcx.associated_item(item_def_id).container.id());
                    let specialized_substs = self.specialize_substs(projection.substs, map);
                    if let Some(instance) = rustc::ty::Instance::resolve(
                        self.tcx,
                        param_env,
                        item_def_id,
                        specialized_substs,
                    ) {
                        let item_def_id = instance.def.def_id();
                        let item_type = self.tcx.type_of(item_def_id);
                        self.specialize_generic_argument_type(item_type, map)
                    } else {
                        debug!("could not resolve an associated type with concrete type arguments");
                        gen_arg_type
                    }
                } else {
                    self.tcx
                        .mk_projection(projection.item_def_id, specialized_substs)
                }
            }
            TyKind::Opaque(def_id, substs) => self
                .tcx
                .mk_opaque(def_id, self.specialize_substs(substs, map)),
            TyKind::Param(ParamTy { name, .. }) => {
                if let Some(ty) = map.as_ref().unwrap().get(&name) {
                    return *ty;
                }
                gen_arg_type
            }
            _ => gen_arg_type,
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

    /// Synthesizes a constant value. Also used for static variable values.
    #[logfn_inputs(TRACE)]
    fn visit_constant(
        &mut self,
        user_ty: Option<UserTypeAnnotationIndex>,
        literal: &Const<'tcx>,
    ) -> Rc<AbstractValue> {
        let ty = literal.ty;

        match &literal.val {
            rustc::ty::ConstKind::Unevaluated(def_id, substs, promoted) => {
                let substs = self.specialize_substs(substs, &self.generic_argument_map);
                self.substs_cache.insert(*def_id, substs);
                let name = utils::summary_key_str(self.tcx, *def_id);
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
                            expression_type: expression_type.clone(),
                        }
                        .into(),
                    ),
                };
                self.lookup_path_and_refine_result(path, expression_type)
            }

            _ => {
                let result;
                match ty.kind {
                    TyKind::Bool
                    | TyKind::Char
                    | TyKind::Float(..)
                    | TyKind::Int(..)
                    | TyKind::Uint(..) => {
                        if let rustc::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Raw {
                            data,
                            size,
                        })) = &literal.val
                        {
                            result = self.get_constant_from_scalar(&ty.kind, *data, *size);
                        } else {
                            assume_unreachable!()
                        }
                    }
                    TyKind::FnDef(def_id, substs)
                    | TyKind::Closure(def_id, substs)
                    | TyKind::Generator(def_id, substs, ..) => {
                        let substs = self.specialize_substs(substs, &self.generic_argument_map);
                        result = self.visit_function_reference(def_id, ty, substs);
                    }
                    TyKind::Ref(
                        _,
                        &rustc::ty::TyS {
                            kind: TyKind::Str, ..
                        },
                        _,
                    ) => {
                        result = if let rustc::ty::ConstKind::Value(ConstValue::Slice {
                            data,
                            start,
                            end,
                        }) = &literal.val
                        {
                            // The rust compiler should ensure this.
                            assume!(*end >= *start);
                            let slice_len = *end - *start;
                            let bytes = data
                                .get_bytes(
                                    &self.tcx,
                                    // invent a pointer, only the offset is relevant anyway
                                    mir::interpret::Pointer::new(
                                        mir::interpret::AllocId(0),
                                        rustc::ty::layout::Size::from_bytes(*start as u64),
                                    ),
                                    rustc::ty::layout::Size::from_bytes(slice_len as u64),
                                )
                                .unwrap();

                            let slice = &bytes[*start..*end];
                            let s = std::str::from_utf8(slice).expect("non utf8 str");
                            let len_val: Rc<AbstractValue> =
                                Rc::new(ConstantDomain::U128(s.len() as u128).into());
                            let res = &mut self.constant_value_cache.get_string_for(s);

                            let path = Path::new_constant(Rc::new(res.clone().into()));
                            let len_path = Path::new_length(path, &self.current_environment);
                            self.current_environment.update_value_at(len_path, len_val);

                            res
                        } else {
                            debug!("unsupported val of type Ref: {:?}", literal);
                            unimplemented!();
                        };
                    }
                    TyKind::Ref(
                        _,
                        &rustc::ty::TyS {
                            kind: TyKind::Array(elem_type, length),
                            ..
                        },
                        _,
                    ) => {
                        return self.visit_reference_to_array_constant(literal, elem_type, length);
                    }
                    TyKind::Ref(
                        _,
                        &rustc::ty::TyS {
                            kind: TyKind::Slice(elem_type),
                            ..
                        },
                        _,
                    ) => match &literal.val {
                        rustc::ty::ConstKind::Value(ConstValue::Slice { data, start, end }) => {
                            // The rust compiler should ensure this.
                            assume!(*end >= *start);
                            let slice_len = *end - *start;
                            let bytes = data
                                .get_bytes(
                                    &self.tcx,
                                    // invent a pointer, only the offset is relevant anyway
                                    mir::interpret::Pointer::new(
                                        mir::interpret::AllocId(0),
                                        rustc::ty::layout::Size::from_bytes(*start as u64),
                                    ),
                                    rustc::ty::layout::Size::from_bytes(slice_len as u64),
                                )
                                .unwrap();

                            let slice = &bytes[*start..*end];
                            let e_type = ExpressionType::from(&elem_type.kind);
                            return self.deconstruct_constant_array(slice, e_type, None);
                        }
                        rustc::ty::ConstKind::Value(ConstValue::ByRef { alloc, offset }) => {
                            let e_type = ExpressionType::from(&elem_type.kind);
                            let id = self.tcx.alloc_map.lock().create_memory_alloc(alloc);
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
                                    &self.tcx,
                                    ptr,
                                    rustc::ty::layout::Size::from_bytes(num_bytes),
                                )
                                .unwrap();
                            return self.deconstruct_constant_array(&bytes, e_type, None);
                        }
                        _ => {
                            debug!("unsupported val of type Ref: {:?}", literal);
                            unimplemented!();
                        }
                    },
                    TyKind::RawPtr(rustc::ty::TypeAndMut {
                        ty,
                        mutbl: rustc_hir::Mutability::Mut,
                    })
                    | TyKind::Ref(_, ty, rustc_hir::Mutability::Mut) => match &literal.val {
                        rustc::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Ptr(p))) => {
                            let summary_cache_key = format!("{:?}", p).into();
                            let expression_type: ExpressionType = ExpressionType::from(&ty.kind);
                            let path = Rc::new(
                                PathEnum::StaticVariable {
                                    def_id: None,
                                    summary_cache_key,
                                    expression_type: expression_type.clone(),
                                }
                                .into(),
                            );
                            return self.lookup_path_and_refine_result(path, expression_type);
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
                            rustc::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Raw {
                                size: 0,
                                ..
                            })) => {
                                return self.get_new_heap_block(
                                    Rc::new(0u128.into()),
                                    Rc::new(1u128.into()),
                                    false,
                                );
                            }
                            _ => {
                                debug!("span: {:?}", self.current_span);
                                debug!("type kind {:?}", ty.kind);
                                debug!("unimplemented constant {:?}", literal);
                                result = &ConstantDomain::Unimplemented;
                            }
                        };
                    }
                    _ => {
                        debug!("span: {:?}", self.current_span);
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
        literal: &rustc::ty::Const<'tcx>,
        ty: Ty<'tcx>,
    ) -> Rc<AbstractValue> {
        match &literal.val {
            rustc::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Ptr(p))) => {
                if let Some(rustc::mir::interpret::GlobalAlloc::Static(def_id)) =
                    self.tcx.alloc_map.lock().get(p.alloc_id)
                {
                    let name = utils::summary_key_str(self.tcx, def_id);
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
                debug!("span: {:?}", self.current_span);
                debug!("type kind {:?}", ty.kind);
                debug!("ptr {:?}", p);
                assume_unreachable!();
            }
            rustc::ty::ConstKind::Value(ConstValue::Slice { data, start, end }) => {
                self.get_value_from_slice(&ty.kind, *data, *start, *end)
            }
            _ => {
                debug!("span: {:?}", self.current_span);
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
        literal: &rustc::ty::Const<'tcx>,
        ty: Ty<'tcx>,
    ) -> Rc<AbstractValue> {
        let result;
        match &literal.val {
            rustc::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Raw { data, size }))
                if *size == 1 =>
            {
                let e =
                    self.get_new_heap_block(Rc::new(1u128.into()), Rc::new(1u128.into()), false);
                if let Expression::HeapBlock { .. } = &e.expression {
                    let p = Path::new_discriminant(
                        Rc::new(Path::get_as_path(e.clone())),
                        &self.current_environment,
                    );
                    let d = Rc::new(self.constant_value_cache.get_u128_for(*data).clone().into());
                    self.current_environment.update_value_at(p, d);
                    return e;
                }
                verify_unreachable!();
            }
            _ => {
                debug!("span: {:?}", self.current_span);
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
                .constant_value_cache
                .get_char_for(char::try_from(data as u32).unwrap()),
            TyKind::Float(..) => match size {
                4 => &mut self.constant_value_cache.get_f32_for(data as u32),
                _ => &mut self.constant_value_cache.get_f64_for(data as u64),
            },
            TyKind::Int(..) => {
                let value: i128 = match size {
                    1 => i128::from(data as i8),
                    2 => i128::from(data as i16),
                    4 => i128::from(data as i32),
                    8 => i128::from(data as i64),
                    _ => data as i128,
                };
                &mut self.constant_value_cache.get_i128_for(value)
            }
            TyKind::Uint(..) => &mut self.constant_value_cache.get_u128_for(data),
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
                &self.tcx,
                // invent a pointer, only the offset is relevant anyway
                mir::interpret::Pointer::new(
                    mir::interpret::AllocId(0),
                    rustc::ty::layout::Size::from_bytes(start as u64),
                ),
                rustc::ty::layout::Size::from_bytes(slice_len as u64),
            )
            .unwrap();
        let slice = &bytes[start..end];
        match ty {
            TyKind::Ref(_, ty, _) => match ty.kind {
                TyKind::Array(elem_type, ..) | TyKind::Slice(elem_type) => {
                    self.deconstruct_constant_array(slice, (&elem_type.kind).into(), None)
                }
                TyKind::Str => {
                    let s = std::str::from_utf8(slice).expect("non utf8 str");
                    let len_val: Rc<AbstractValue> =
                        Rc::new(ConstantDomain::U128(s.len() as u128).into());
                    let res: Rc<AbstractValue> =
                        Rc::new(self.constant_value_cache.get_string_for(s).clone().into());

                    let path = Path::new_constant(res.clone());
                    let len_path = Path::new_length(path, &self.current_environment);
                    self.current_environment.update_value_at(len_path, len_val);
                    res
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
        literal: &rustc::ty::Const<'tcx>,
        elem_type: &rustc::ty::TyS<'tcx>,
        length: &rustc::ty::Const<'tcx>,
    ) -> Rc<AbstractValue> {
        use rustc::mir::interpret::{ConstValue, Scalar};

        if let rustc::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Raw { data, .. }, ..)) =
            &length.val
        {
            let len = *data;
            let e_type = ExpressionType::from(&elem_type.kind);
            match &literal.val {
                rustc::ty::ConstKind::Value(ConstValue::Slice { data, start, end }) => {
                    // The Rust compiler should ensure this.
                    assume!(*end > *start);
                    let slice_len = *end - *start;
                    let bytes = data
                        .get_bytes(
                            &self.tcx,
                            // invent a pointer, only the offset is relevant anyway
                            mir::interpret::Pointer::new(
                                mir::interpret::AllocId(0),
                                rustc::ty::layout::Size::from_bytes(*start as u64),
                            ),
                            rustc::ty::layout::Size::from_bytes(slice_len as u64),
                        )
                        .unwrap();
                    let slice = &bytes[*start..*end];
                    self.deconstruct_constant_array(slice, e_type, Some(len))
                }
                rustc::ty::ConstKind::Value(ConstValue::ByRef { alloc, offset }) => {
                    //todo: there is no test coverage for this case
                    let id = self.tcx.alloc_map.lock().create_memory_alloc(alloc);
                    let alloc_len = alloc.len() as u64;
                    let offset_bytes = offset.bytes();
                    // The Rust compiler should ensure this.
                    assume!(alloc_len > offset_bytes);
                    let num_bytes = alloc_len - offset_bytes;
                    let ptr = mir::interpret::Pointer::new(
                        id,
                        rustc::ty::layout::Size::from_bytes(offset.bytes()),
                    );
                    //todo: this is all wrong. It gets the bytes that contains the reference,
                    // not the bytes that the reference points to.
                    // Right now it is not clear how to implement this.
                    // Keeping this wrong behavior maintains the currently incorrect status quo.
                    let bytes = alloc
                        .get_bytes_with_undef_and_ptr(
                            &self.tcx,
                            ptr,
                            rustc::ty::layout::Size::from_bytes(num_bytes),
                        )
                        .unwrap();
                    self.deconstruct_constant_array(&bytes, e_type, Some(len))
                }
                rustc::ty::ConstKind::Value(ConstValue::Scalar(mir::interpret::Scalar::Ptr(
                    ptr,
                ))) => {
                    if let Some(rustc::mir::interpret::GlobalAlloc::Static(def_id)) =
                        self.tcx.alloc_map.lock().get(ptr.alloc_id)
                    {
                        let name = utils::summary_key_str(self.tcx, def_id);
                        let path = Rc::new(
                            PathEnum::StaticVariable {
                                def_id: Some(def_id),
                                summary_cache_key: name,
                                expression_type: ExpressionType::NonPrimitive,
                            }
                            .into(),
                        );
                        return self
                            .lookup_path_and_refine_result(path, ExpressionType::NonPrimitive);
                    }
                    let alloc = self.tcx.alloc_map.lock().unwrap_memory(ptr.alloc_id);
                    let alloc_len = alloc.len() as u64;
                    let offset_bytes = ptr.offset.bytes();
                    // The Rust compiler should ensure this.
                    assume!(alloc_len > offset_bytes);
                    let num_bytes = alloc_len - offset_bytes;
                    let bytes = alloc
                        .get_bytes(
                            &self.tcx,
                            *ptr,
                            rustc::ty::layout::Size::from_bytes(num_bytes),
                        )
                        .unwrap();
                    self.deconstruct_constant_array(&bytes, e_type, Some(len))
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
    fn deconstruct_constant_array(
        &mut self,
        bytes: &[u8],
        elem_type: ExpressionType,
        len: Option<u128>,
    ) -> Rc<AbstractValue> {
        let byte_len = bytes.len();
        let alignment = Rc::new(((elem_type.bit_length() / 8) as u128).into());
        let array_value =
            self.get_new_heap_block(Rc::new((byte_len as u128).into()), alignment, false);
        if byte_len > k_limits::MAX_BYTE_ARRAY_LENGTH {
            return array_value;
        }
        let array_path: Rc<Path> = Rc::new(Path::get_as_path(array_value));
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
            let index_path =
                Path::new_index(array_path.clone(), index_value, &self.current_environment);
            self.current_environment
                .update_value_at(index_path, operand);
        }
        let length_path = Path::new_length(array_path.clone(), &self.current_environment);
        let length_value = Rc::new(
            self.constant_value_cache
                .get_u128_for(last_index + 1)
                .clone()
                .into(),
        );
        self.current_environment
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
        self.substs_cache.insert(def_id, generic_args);
        &mut self.constant_value_cache.get_function_constant_for(
            def_id,
            ty,
            generic_args,
            self.tcx,
            self.known_names_cache,
            self.summary_cache,
        )
    }

    /// Returns a Path instance that is the essentially the same as the Place instance, but which
    /// can be serialized and used as a cache key. Also caches the place type with the path as key.
    #[logfn_inputs(TRACE)]
    fn visit_place(&mut self, place: &mir::Place<'tcx>) -> Rc<Path> {
        let path = self.get_path_for_place(place);
        let ty = self.get_rustc_place_type(place);
        self.path_ty_cache.insert(path.clone(), ty);
        path
    }

    /// Returns a Path instance that is the essentially the same as the Place instance, but which
    /// can be serialized and used as a cache key.
    #[logfn(TRACE)]
    fn get_path_for_place(&mut self, place: &mir::Place<'tcx>) -> Rc<Path> {
        let mut is_union = false;
        let base_path: Rc<Path> =
            Path::new_local_parameter_or_result(place.local.as_usize(), self.mir.arg_count);
        if place.projection.is_empty() {
            let ty = self.get_rustc_place_type(place);
            match &ty.kind {
                TyKind::Adt(def, ..) => {
                    let ty_name = self.known_names_cache.get(self.tcx, def.did);
                    if ty_name == KnownNames::StdMarkerPhantomData {
                        return Rc::new(PathEnum::PhantomData.into());
                    }
                }
                TyKind::Array(_, len) => {
                    let len_val = self.visit_constant(None, &len);
                    let len_path = Path::new_length(base_path.clone(), &self.current_environment);
                    self.current_environment.update_value_at(len_path, len_val);
                }
                TyKind::Closure(def_id, generic_args, ..) => {
                    let func_const = self.visit_function_reference(
                        *def_id,
                        ty,
                        generic_args.as_closure().substs,
                    );
                    let func_val = Rc::new(func_const.clone().into());
                    self.current_environment
                        .update_value_at(base_path.clone(), func_val);
                }
                TyKind::FnDef(def_id, generic_args) => {
                    let func_const = self.visit_function_reference(
                        *def_id,
                        ty,
                        generic_args.as_closure().substs,
                    );
                    let func_val = Rc::new(func_const.clone().into());
                    self.current_environment
                        .update_value_at(base_path.clone(), func_val);
                }
                TyKind::Generator(def_id, generic_args, ..) => {
                    let func_const = self.visit_function_reference(
                        *def_id,
                        ty,
                        generic_args.as_generator().substs,
                    );
                    let func_val = Rc::new(func_const.clone().into());
                    self.current_environment
                        .update_value_at(base_path.clone(), func_val);
                }
                _ => (),
            }
        } else {
            let ty = self.mir.local_decls[place.local].ty;
            is_union = Self::is_union(ty);
        }
        self.visit_projection(base_path, is_union, &place.projection)
    }

    /// Returns true if the ty is a union.
    fn is_union(ty: Ty<'_>) -> bool {
        if let TyKind::Adt(def, ..) = ty.kind {
            def.is_union()
        } else {
            false
        }
    }

    /// Returns a path that is qualified by the selector corresponding to projection.elem.
    /// If projection has a base, the give base_path is first qualified with the base.
    #[logfn_inputs(TRACE)]
    fn visit_projection(
        &mut self,
        base_path: Rc<Path>,
        mut base_is_union: bool,
        projection: &[mir::PlaceElem<'tcx>],
    ) -> Rc<Path> {
        projection.iter().fold(base_path, |base_path, elem| {
            let selector = self.visit_projection_elem(&mut base_is_union, &elem);
            Path::new_qualified(base_path, Rc::new(selector))
                .refine_paths(&self.current_environment)
        })
    }

    /// Returns a PathSelector instance that is essentially the same as the ProjectionElem instance
    /// but which can be serialized.
    #[logfn_inputs(TRACE)]
    fn visit_projection_elem(
        &mut self,
        base_is_union: &mut bool,
        projection_elem: &mir::ProjectionElem<mir::Local, &rustc::ty::TyS<'tcx>>,
    ) -> PathSelector {
        match projection_elem {
            mir::ProjectionElem::Deref => PathSelector::Deref,
            mir::ProjectionElem::Field(field, field_ty) => {
                let r = PathSelector::Field(if *base_is_union { 0 } else { field.index() });
                *base_is_union = Self::is_union(*field_ty);
                r
            }
            mir::ProjectionElem::Index(local) => {
                let local_path =
                    Path::new_local_parameter_or_result(local.as_usize(), self.mir.arg_count);
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

    /// Returns an ExpressionType value corresponding to the Rustc type of the place.
    #[logfn_inputs(TRACE)]
    fn get_place_type(&mut self, place: &mir::Place<'tcx>) -> ExpressionType {
        (&self.get_rustc_place_type(place).kind).into()
    }

    /// Returns the rustc Ty of the given place in memory.
    #[logfn_inputs(TRACE)]
    #[logfn(TRACE)]
    fn get_rustc_place_type(&self, place: &mir::Place<'tcx>) -> Ty<'tcx> {
        let result = {
            let base_type = self.mir.local_decls[place.local].ty;
            self.get_type_for_projection_element(base_type, &place.projection)
        };
        match result.kind {
            TyKind::Param(t_par) => {
                if let Some(generic_args) = self.generic_arguments {
                    if let Some(gen_arg) = generic_args.as_ref().get(t_par.index as usize) {
                        return gen_arg.expect_ty();
                    }
                    if t_par.name.as_str() == "Self" && !self.actual_argument_types.is_empty() {
                        return self.actual_argument_types[0];
                    }
                }
            }
            TyKind::Ref(region, ty, mutbl) => {
                if let TyKind::Param(t_par) = ty.kind {
                    if t_par.name.as_str() == "Self" && !self.actual_argument_types.is_empty() {
                        return self.tcx.mk_ref(
                            region,
                            rustc::ty::TypeAndMut {
                                ty: self.actual_argument_types[0],
                                mutbl,
                            },
                        );
                    }
                }
            }
            _ => {}
        }
        result
    }

    /// This is a hacky and brittle way to navigate the Rust compiler's type system.
    /// Eventually it should be replaced with a comprehensive and principled mapping.
    #[logfn_inputs(TRACE)]
    fn get_path_rustc_type(&mut self, path: &Rc<Path>) -> Ty<'tcx> {
        if let Some(ty) = self.path_ty_cache.get(path) {
            return ty;
        }
        match &path.value {
            PathEnum::LocalVariable { ordinal } => {
                if *ordinal > 0 && *ordinal < self.mir.local_decls.len() {
                    self.mir.local_decls[mir::Local::from(*ordinal)].ty
                } else {
                    info!("path.value is {:?}", path.value);
                    self.tcx.mk_ty(TyKind::Error)
                }
            }
            PathEnum::Parameter { ordinal } => {
                if self.actual_argument_types.len() >= *ordinal {
                    self.actual_argument_types[*ordinal - 1]
                } else if *ordinal > 0 && *ordinal < self.mir.local_decls.len() {
                    self.mir.local_decls[mir::Local::from(*ordinal)].ty
                } else {
                    info!("path.value is {:?}", path.value);
                    self.tcx.mk_ty(TyKind::Error)
                }
            }
            PathEnum::Result => {
                if self.mir.local_decls.is_empty() {
                    info!("result type wanted from function without result local");
                    self.tcx.mk_ty(TyKind::Error)
                } else {
                    self.mir.local_decls[mir::Local::from(0usize)].ty
                }
            }
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                let t = self.get_path_rustc_type(qualifier);
                match &**selector {
                    PathSelector::ConstantSlice { .. } | PathSelector::Slice(_) => {
                        return t;
                    }
                    PathSelector::Field(ordinal) => {
                        let bt = Self::get_dereferenced_type(t);
                        match &bt.kind {
                            TyKind::Adt(AdtDef { variants, .. }, substs) => {
                                if !Self::is_union(bt) {
                                    if let Some(variant_index) = variants.last() {
                                        let variant = &variants[variant_index];
                                        if *ordinal < variant.fields.len() {
                                            let field = &variant.fields[*ordinal];
                                            return field.ty(self.tcx, substs);
                                        }
                                    }
                                }
                            }
                            TyKind::Closure(.., subs) => {
                                if *ordinal + 4 < subs.len() {
                                    return subs.as_ref()[*ordinal + 4].expect_ty();
                                }
                            }
                            TyKind::Tuple(types) => {
                                if let Some(gen_arg) = types.get(*ordinal as usize) {
                                    return gen_arg.expect_ty();
                                }
                            }
                            _ => (),
                        }
                    }
                    PathSelector::Deref => {
                        return Self::get_dereferenced_type(t);
                    }
                    PathSelector::Discriminant => {
                        return self.tcx.types.i32;
                    }
                    PathSelector::Downcast(_, ordinal) => {
                        if let TyKind::Adt(def, substs) = &t.kind {
                            use rustc_index::vec::Idx;
                            let variant = &def.variants[VariantIdx::new(*ordinal)];
                            let field_tys = variant.fields.iter().map(|fd| fd.ty(self.tcx, substs));
                            return self.tcx.mk_tup(field_tys);
                        }
                    }
                    PathSelector::Index(_) => match &t.kind {
                        TyKind::Array(elem_ty, _) | TyKind::Slice(elem_ty) => {
                            return elem_ty;
                        }
                        _ => (),
                    },
                    _ => {}
                }
                info!("current span is {:?}", self.current_span);
                info!("t is {:?}", t);
                info!("qualifier is {:?}", qualifier);
                info!("selector is {:?}", selector);
                self.tcx.mk_ty(TyKind::Error)
            }
            PathEnum::StaticVariable { def_id, .. } => {
                if let Some(def_id) = def_id {
                    return self.tcx.type_of(*def_id);
                }
                info!("path.value is {:?}", path.value);
                self.tcx.mk_ty(TyKind::Error)
            }
            _ => {
                info!("path.value is {:?}", path.value);
                self.tcx.mk_ty(TyKind::Error)
            }
        }
    }

    /// Returns the target type of a reference type.
    fn get_dereferenced_type(ty: Ty<'tcx>) -> Ty<'tcx> {
        match &ty.kind {
            TyKind::Ref(_, t, _) => *t,
            _ => ty,
        }
    }

    /// Returns the element type of an array or slice type.
    fn get_element_type(ty: Ty<'tcx>) -> Ty<'tcx> {
        match &ty.kind {
            TyKind::Array(t, _) => *t,
            TyKind::Ref(_, t, _) => match &t.kind {
                TyKind::Array(t, _) => *t,
                TyKind::Slice(t) => *t,
                _ => t,
            },
            TyKind::Slice(t) => *t,
            _ => ty,
        }
    }

    /// Returns the rustc TyKind of the element selected by projection_elem.
    #[logfn_inputs(TRACE)]
    fn get_type_for_projection_element(
        &self,
        base_ty: Ty<'tcx>,
        place_projection: &[rustc::mir::PlaceElem<'tcx>],
    ) -> Ty<'tcx> {
        place_projection
            .iter()
            .fold(base_ty, |base_ty, projection_elem| match projection_elem {
                mir::ProjectionElem::Deref => match &base_ty.kind {
                    TyKind::Adt(..) => base_ty,
                    TyKind::RawPtr(ty_and_mut) => ty_and_mut.ty,
                    TyKind::Ref(_, ty, _) => *ty,
                    _ => {
                        debug!(
                            "span: {:?}\nelem: {:?} type: {:?}",
                            self.current_span, projection_elem, base_ty
                        );
                        assume_unreachable!();
                    }
                },
                mir::ProjectionElem::Field(_, ty) => ty,
                mir::ProjectionElem::Index(_)
                | mir::ProjectionElem::ConstantIndex { .. }
                | mir::ProjectionElem::Subslice { .. } => match &base_ty.kind {
                    TyKind::Adt(..) => base_ty,
                    TyKind::Array(ty, _) => *ty,
                    TyKind::Ref(_, ty, _) => Self::get_element_type(*ty),
                    TyKind::Slice(ty) => *ty,
                    _ => {
                        debug!(
                            "span: {:?}\nelem: {:?} type: {:?}",
                            self.current_span, projection_elem, base_ty
                        );
                        assume_unreachable!();
                    }
                },
                mir::ProjectionElem::Downcast(..) => base_ty,
            })
    }
}
