// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::abstract_value::AbstractValue;
use crate::abstract_value::AbstractValueTrait;
use crate::constant_domain::FunctionReference;
use crate::environment::Environment;
use crate::expression::Expression;
use crate::path::{Path, PathEnum, PathSelector};
use crate::utils;

use itertools::Itertools;
use log_derive::{logfn, logfn_inputs};
use mirai_annotations::*;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Ty, TyCtxt};
use serde::{Deserialize, Serialize};
use sled::{Config, Db};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Formatter, Result};
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::rc::Rc;

/// A summary is a declarative abstract specification of what a function does.
/// This is calculated once per function and is used by callers of the function.
/// Callers will specialize this summary by replacing embedded parameter values with the corresponding
/// argument values and then simplifying the resulting values under the current path condition.
///
/// Summaries are stored in a persistent, per project database. When a crate is recompiled,
/// all summaries arising from the crate are recomputed, but the database is only updated when
/// a function summary changes. When this happens, all callers of the function need to be reanalyzed
/// using the new summary, which could result in their summaries being updated, and so on.
/// In the case of recursive loops, a function summary may need to be recomputed and widened
/// until a fixed point is reached. Since crate dependencies are acyclic, fixed point computation
/// can be limited to the functions of one crate and the dependency graph need not be stored
/// in the database.
///
/// There are three ways summaries are constructed:
/// 1) By analyzing the body of the actual function.
/// 2) By analyzing the body of a contract function that contains only enough code to generate
///    an accurate summary. This is the preferred way to deal with abstract and foreign functions
///    where the actual body is not known until runtime.
/// 3) By constructing a dummy summary using only the type signature of the function.
///    In such cases there are no preconditions, no post conditions, the result value is fully
///    abstract as is the unwind condition and the values assigned to any mutable parameter.
///    This makes the summary a conservative over approximation of the actual behavior. It is not
///    sound, however, if there are side effects on static state since it is neither practical nor
///    desirable to havoc all static variables every time such a function is called. Consequently
///    sound analysis is only possible if one can assume that all such functions have been provided
///    with explicit contract functions.
#[derive(Serialize, Deserialize, Clone, Debug, Default, Eq, PartialEq)]
pub struct Summary {
    /// If true this summary was computed. If false, it is a default summary.
    /// Used to distinguish a computed empty summary from a default summary.
    /// In the latter case, the summary should be computed from MIR, if available.
    /// If no MIR is available, the summary is left empty but marked as is_computed so that
    /// there are no repeated attempts at recomputing the summary.
    pub is_computed: bool,

    /// If true, the summary is incomplete, which means that the result and side-effects could be
    /// over specific because widening did not happen and also that some side-effects may be missing.
    /// The summary may also fail to mention necessary preconditions or useful post conditions.
    /// This happens if the computation of this summary failed for some reason, for example
    /// no MIR body or a time-out.
    /// A function that makes use of an incomplete summary cannot be fully analyzed and thus becomes
    /// incomplete in turn.
    pub is_incomplete: bool,

    // Conditions that should hold prior to the call.
    // Callers should substitute parameter values with argument values and simplify the results
    // under the current path condition. Any values that do not simplify to true will require the
    // caller to either generate an error message or to add a precondition to its own summary that
    // will be sufficient to ensure that all of the preconditions in this summary are met.
    // The string value bundled with the condition is the message that details what would go
    // wrong at runtime if the precondition is not satisfied by the caller.
    pub preconditions: Vec<Precondition>,

    // Modifications the function makes to mutable state external to the function.
    // Every path will be rooted in a static or in a mutable parameter.
    // No two paths in this collection will lead to the same place in memory.
    // Callers should substitute parameter values with argument values and simplify the results
    // under the current path condition. They should then update their current state to reflect the
    // side-effects of the call.
    pub side_effects: Vec<(Rc<Path>, Rc<AbstractValue>)>,

    // A condition that should hold subsequent to a call that completes normally.
    // Callers should substitute parameter values with argument values and simplify the results
    // under the current path condition.
    // The resulting value should be conjoined to the current path condition.
    pub post_condition: Option<Rc<AbstractValue>>,

    /// The type table index for the Rust type of the actual return value.
    /// Used to make type tracking more precise when the body returns a value of concrete type
    /// but the return type specification is abstract.
    #[serde(skip)]
    pub return_type_index: usize,
}

/// Bundles together the condition of a precondition with the provenance (place where defined) of
/// the condition, along with a diagnostic message to use when the precondition is not (might not be)
/// satisfied.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Precondition {
    /// The condition that must be satisfied when calling a function that has this precondition.
    pub condition: Rc<AbstractValue>,
    /// A diagnostic message to issue if the precondition is not met.
    pub message: Rc<str>,
    /// The source location of the precondition definition (or the source expression/statement that
    /// would panic if the precondition is not met). This is in textual form because it needs to be
    /// persistable and crate independent.
    pub provenance: Option<Rc<str>>,
    /// A stack of source locations that lead to the definition of the precondition (or the source
    /// expression/statement that would panic if the precondition is not met). It is a stack
    /// because the precondition might have been promoted (when a non public function does not meet
    /// a precondition of a function it calls, MIRAI infers a precondition that will allow it to
    /// meet the precondition of the call, so things stack up).
    /// Because this situation arises for non public functions, it is possible to use source spans
    /// rather than strings to track the locations where the promotions happen.
    #[serde(skip)]
    pub spans: Vec<rustc_span::Span>,
}

impl Summary {
    #[logfn_inputs(TRACE)]
    pub fn is_subset_of(&self, other: &Summary) -> bool {
        if !Self::is_subset_of_preconditions(&self.preconditions[0..], &other.preconditions[0..]) {
            return false;
        }
        if !Self::is_subset_of_side_effects(&self.side_effects[0..], &other.side_effects[0..]) {
            return false;
        }
        true
    }

    #[logfn_inputs(TRACE)]
    fn is_subset_of_preconditions(p1: &[Precondition], p2: &[Precondition]) -> bool {
        if p1.is_empty() {
            return true;
        }
        if p2.is_empty() {
            return false;
        }
        if p1[0].spans < p2[0].spans {
            return false;
        }
        if p1[0].spans > p2[0].spans {
            return Self::is_subset_of_preconditions(p1, &p2[1..]);
        }
        if !p1[0].condition.subset(&p2[0].condition) {
            return false;
        }
        Self::is_subset_of_preconditions(&p1[1..], &p2[1..])
    }

    #[logfn_inputs(TRACE)]
    fn is_subset_of_side_effects(
        e1: &[(Rc<Path>, Rc<AbstractValue>)],
        e2: &[(Rc<Path>, Rc<AbstractValue>)],
    ) -> bool {
        if e1.is_empty() {
            return true;
        }
        if e2.is_empty() {
            return false;
        }
        let (p1, v1) = &e1[0];
        let (p2, v2) = &e2[0];
        if p1 < p2 {
            return false;
        }
        if p1 > p2 {
            return Self::is_subset_of_side_effects(e1, &e2[1..]);
        }
        if !v1.subset(v2) {
            return false;
        }
        Self::is_subset_of_side_effects(&e1[1..], &e2[1..])
    }

    pub fn join_side_effects(&mut self, other: &Summary) {
        let other_map: HashMap<Rc<Path>, Rc<AbstractValue>> =
            other.side_effects.clone().into_iter().collect();
        for (path, val1) in self.side_effects.iter_mut() {
            match other_map.get(path) {
                Some(val2) => {
                    *val1 = val1.join((*val2).clone(), path);
                }
                None => {
                    if path.is_rooted_by_parameter() {
                        let val2 = AbstractValue::make_initial_parameter_value(
                            val1.expression.infer_type(),
                            path.clone(),
                        );
                        *val1 = val1.join(val2, path);
                    };
                }
            }
        }
    }

    pub fn widen_side_effects(&mut self) {
        for (path, value) in self.side_effects.iter_mut() {
            *value = value.widen(path);
        }
    }
}

/// Constructs a summary of a function body by processing state information gathered during
/// abstract interpretation of the body.
#[allow(clippy::too_many_arguments)]
#[logfn(TRACE)]
pub fn summarize(
    argument_count: usize,
    exit_environment: Option<&Environment>,
    preconditions: &[Precondition],
    post_condition: &Option<Rc<AbstractValue>>,
    return_type_index: usize,
    tcx: TyCtxt<'_>,
) -> Summary {
    trace!(
        "summarize env {:?} pre {:?} post {:?}",
        exit_environment,
        preconditions,
        post_condition,
    );
    let mut preconditions: Vec<Precondition> = add_provenance(preconditions, tcx);
    let mut side_effects = if let Some(exit_environment) = exit_environment {
        extract_side_effects(exit_environment, argument_count)
    } else {
        vec![]
    };

    preconditions.sort();
    side_effects.sort();

    Summary {
        is_computed: true,
        is_incomplete: false,
        preconditions,
        side_effects,
        post_condition: post_condition.clone(),
        return_type_index,
    }
}

/// When a precondition is being serialized into a summary, it needs a provenance that is not
/// specific to the current (crate) compilation, since the summary may be used to compile a different
/// crate, or a different version of the current crate.
#[logfn(TRACE)]
fn add_provenance(preconditions: &[Precondition], tcx: TyCtxt<'_>) -> Vec<Precondition> {
    preconditions
        .iter()
        .map(|precondition| {
            let mut precond = precondition.clone();
            if !precondition.spans.is_empty() {
                let last_span = precondition.spans.last();
                let span = last_span.unwrap().source_callsite();
                precond.provenance = Some(Rc::from(
                    tcx.sess
                        .source_map()
                        .span_to_diagnostic_string(span)
                        .as_str(),
                ));
            }
            precond
        })
        .collect()
}

/// Returns a list of (path, value) pairs where each path is rooted by an argument(or the result)
/// or where the path root is a heap block reachable from an argument (or the result).
/// Since paths are created by writes, these are side-effects.
/// Since these values are reachable from arguments or the result, they are visible to the caller
/// and must be included in the summary.
#[logfn_inputs(TRACE)]
fn extract_side_effects(
    env: &Environment,
    argument_count: usize,
) -> Vec<(Rc<Path>, Rc<AbstractValue>)> {
    let mut heap_roots: HashSet<Rc<AbstractValue>> = HashSet::new();
    let mut result = Vec::new();
    for ordinal in 0..=argument_count {
        let root = if ordinal == 0 {
            Path::new_result()
        } else {
            Path::new_parameter(ordinal)
        };
        for (path, value) in env
            .value_map
            .iter()
            .filter(|(p, _)| (ordinal == 0 && (**p) == root) || p.is_rooted_by(&root))
            .sorted_by(|(p1, _), (p2, _)| {
                let len1 = p1.path_length();
                let len2 = p2.path_length();
                if len1 == len2 {
                    if matches!(&p1.value, PathEnum::QualifiedPath { selector, .. } if **selector == PathSelector::Deref) {
                        Ordering::Less
                    } else {
                        Ordering::Equal
                    }
                } else {
                    len1.cmp(&len2)
                }
            })
        {
            path.record_heap_blocks_and_strings(&mut heap_roots);
            value.record_heap_blocks_and_strings(&mut heap_roots);
            if let Expression::Variable { path: vpath, .. } | Expression::InitialParameterValue { path: vpath, ..} = &value.expression {
                if ordinal > 0 && vpath.eq(path) {
                    // The value is not an update, but just what was there at function entry.
                    continue;
                }
            }
            result.push((path.clone(), value.clone()));
        }
    }
    extract_reachable_heap_allocations(env, &mut heap_roots, &mut result);
    result
}

/// Adds roots for all new heap allocated objects that are reachable by the caller.
#[logfn_inputs(TRACE)]
fn extract_reachable_heap_allocations(
    env: &Environment,
    heap_roots: &mut HashSet<Rc<AbstractValue>>,
    result: &mut Vec<(Rc<Path>, Rc<AbstractValue>)>,
) {
    let mut visited_heap_roots: HashSet<Rc<AbstractValue>> = HashSet::new();
    while heap_roots.len() > visited_heap_roots.len() {
        let mut new_roots: HashSet<Rc<AbstractValue>> = HashSet::new();
        for heap_root in heap_roots.iter() {
            if visited_heap_roots.insert(heap_root.clone()) {
                let root = Path::get_as_path(heap_root.clone());
                for (path, value) in env
                    .value_map
                    .iter()
                    .filter(|(p, _)| (**p) == root || p.is_rooted_by(&root))
                {
                    path.record_heap_blocks_and_strings(&mut new_roots);
                    value.record_heap_blocks_and_strings(&mut new_roots);
                    result.push((path.clone(), value.clone()));
                }
            }
        }
        heap_roots.extend(new_roots.into_iter());
    }
}

#[derive(PartialEq, Eq)]
pub struct CallSiteKey<'tcx> {
    func_args: Option<Rc<Vec<Rc<FunctionReference>>>>,
    type_cache: Option<Rc<HashMap<Rc<Path>, Ty<'tcx>>>>,
}

impl<'tcx> CallSiteKey<'tcx> {
    pub fn new(
        func_args: Option<Rc<Vec<Rc<FunctionReference>>>>,
        type_cache: Option<Rc<HashMap<Rc<Path>, Ty<'tcx>>>>,
    ) -> CallSiteKey<'tcx> {
        CallSiteKey {
            func_args,
            type_cache,
        }
    }
}

impl<'tcx> Hash for CallSiteKey<'tcx> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        if let Some(func_args) = &self.func_args {
            func_args.hash(state);
        }
        if let Some(cache) = &self.type_cache {
            for (path, ty) in cache.iter() {
                path.hash(state);
                ty.kind().hash(state);
            }
        }
    }
}

/// A persistent map from summary key to Summary, along with a transient cache from DefId to
/// Summary. The latter is cleared after every outer fixed point loop iteration.
/// Also tracks which definitions depend on (use) any particular Summary.
pub struct PersistentSummaryCache<'tcx> {
    db: Db,
    def_id_cache: HashMap<DefId, Summary>,
    typed_cache: HashMap<usize, Summary>,
    typed_cache_table: HashMap<CallSiteKey<'tcx>, HashMap<usize, Summary>>,
    reference_cache: HashMap<Rc<FunctionReference>, Summary>,
    typed_reference_cache: HashMap<Rc<FunctionReference>, Summary>,
    key_cache: HashMap<DefId, Rc<str>>,
    type_context: TyCtxt<'tcx>,
}

impl<'tcx> Debug for PersistentSummaryCache<'tcx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "PersistentSummaryCache".fmt(f)
    }
}

impl<'a, 'tcx: 'a> PersistentSummaryCache<'tcx> {
    /// Creates a new persistent summary cache, using (or creating) a Sled data base at the given
    /// directory path.
    #[logfn(TRACE)]
    pub fn new(
        type_context: TyCtxt<'tcx>,
        summary_store_directory_str: String,
    ) -> PersistentSummaryCache<'tcx> {
        use rand::{thread_rng, Rng};
        use std::thread;
        use std::time::Duration;

        let mut rng = thread_rng();
        let summary_store_path =
            Self::create_default_summary_store_if_needed(&summary_store_directory_str);
        let config = Config::default().path(summary_store_path);
        let mut result;
        loop {
            result = config.open();
            if result.is_ok() {
                break;
            }
            debug!("opening db failed {:?}", result);
            let num_millis = rng.gen_range(100..200);
            thread::sleep(Duration::from_millis(num_millis));
        }
        let db = result.unwrap_or_else(|err| {
            debug!("{} ", err);
            assume_unreachable!();
        });
        PersistentSummaryCache {
            db,
            def_id_cache: HashMap::new(),
            typed_cache: HashMap::new(),
            typed_cache_table: HashMap::new(),
            reference_cache: HashMap::new(),
            typed_reference_cache: HashMap::new(),
            key_cache: HashMap::new(),
            type_context,
        }
    }

    /// Creates a Sled database at the given directory path, if it does not already exist.
    /// The initial value of the database contains summaries of standard library functions.
    /// The code used to create these summaries are mirai/standard_contracts.
    #[logfn_inputs(TRACE)]
    fn create_default_summary_store_if_needed(
        summary_store_directory_str: &str,
    ) -> std::path::PathBuf {
        use std::env;
        use std::fs::File;
        use std::io::Write;
        use std::path::Path;
        use tar::Archive;

        let directory_path = Path::new(summary_store_directory_str);
        let store_path = directory_path.join(".summary_store.sled");
        if env::var("MIRAI_START_FRESH").is_ok() {
            std::fs::remove_dir_all(directory_path).unwrap();
            std::fs::create_dir_all(directory_path).unwrap();
        } else if env::var("MIRAI_SHARE_PERSISTENT_STORE").is_err() {
            info!("creating a new summary store from the embedded tar file");
            {
                let tar_path = directory_path.join(".summary_store.tar");
                let mut tar_file = File::create(tar_path.clone()).unwrap();
                let bytes = include_bytes!("../../binaries/summary_store.tar");
                tar_file.write_all(bytes).unwrap();
                let tar_file = File::open(tar_path).unwrap();
                let mut ar = Archive::new(tar_file);
                ar.unpack(directory_path).unwrap();
            }
        }
        store_path
    }

    /// Returns (and caches) a string that uniquely identifies a definition to serve as a key to
    /// the summary cache, which is a key value store. The string will always be the same as
    /// long as the definition does not change its name or location, so it can be used to
    /// transfer information from one compilation to the next, making incremental analysis possible.
    #[logfn_inputs(TRACE)]
    pub fn get_summary_key_for(&mut self, def_id: DefId) -> &Rc<str> {
        let tcx = self.type_context;
        self.key_cache
            .entry(def_id)
            .or_insert_with(|| utils::summary_key_str(tcx, def_id))
    }

    /// Returns the cached summary corresponding to the function reference.
    /// If the reference has no def_id (and hence no function_id), the entire reference used
    /// as the key, which requires more cache instances and the hard to extract
    /// and unify, duplicated code.
    #[logfn_inputs(TRACE)]
    pub fn get_summary_for_call_site(
        &mut self,
        func_ref: &Rc<FunctionReference>,
        func_args: &Option<Rc<Vec<Rc<FunctionReference>>>>,
        initial_type_cache: &Option<Rc<HashMap<Rc<Path>, Ty<'tcx>>>>,
    ) -> &Summary {
        match (func_ref.def_id, func_ref.function_id) {
            // Use the ids as keys if they are available, since they make much better keys.
            (Some(def_id), Some(function_id)) => {
                if func_args.is_some() || initial_type_cache.is_some() {
                    let typed_cache_key =
                        CallSiteKey::new(func_args.clone(), initial_type_cache.clone());
                    // Need the double lookup in order to allow the recursive call to get_summary_for_function_constant.
                    let summary_is_cached =
                        if let Some(type_table) = self.typed_cache_table.get(&typed_cache_key) {
                            type_table.get(&function_id).is_some()
                        } else {
                            false
                        };
                    return if summary_is_cached {
                        self.typed_cache_table
                            .get(&typed_cache_key)
                            .unwrap()
                            .get(&function_id)
                            .unwrap()
                    } else {
                        // can't have self borrowed at this point.
                        let summary = self
                            .get_summary_for_call_site(func_ref, &None, &None)
                            .clone();
                        self.typed_cache_table
                            .entry(typed_cache_key)
                            .or_insert_with(HashMap::new)
                            .entry(function_id)
                            .or_insert(summary)
                    };
                }

                if self.typed_cache.contains_key(&function_id) {
                    let result = self.typed_cache.get(&function_id);
                    result.expect("value disappeared from typed_cache")
                } else {
                    if let Some(summary) = self.get_persistent_summary_using_arg_types_if_possible(
                        &func_ref.summary_cache_key,
                        &func_ref.argument_type_key,
                    ) {
                        return self.typed_cache.entry(function_id).or_insert(summary);
                    }

                    // In this case we default to the summary that is not argument type specific, but
                    // we need to take care not to cache this summary in self.typed_cache because updating
                    // self.cache will not also update self.typed_cache.
                    let db = &self.db;
                    self.def_id_cache.entry(def_id).or_insert_with(|| {
                        let summary =
                            Self::get_persistent_summary_for_db(db, &func_ref.summary_cache_key);
                        summary.unwrap_or_default()
                    })
                }
            }
            // Use the full function reference structs as keys. This is the slow path and it
            // is only needed for function references that are obtained via deserialization of
            // function summaries.
            _ => {
                if self.typed_reference_cache.contains_key(func_ref) {
                    let result = self.typed_reference_cache.get(func_ref);
                    result.expect("value disappeared from typed_reference_cache")
                } else {
                    if let Some(summary) = self.get_persistent_summary_using_arg_types_if_possible(
                        &func_ref.summary_cache_key,
                        &func_ref.argument_type_key,
                    ) {
                        return self
                            .typed_reference_cache
                            .entry(func_ref.clone())
                            .or_insert(summary);
                    }

                    let db = &self.db;
                    self.reference_cache
                        .entry(func_ref.clone())
                        .or_insert_with(|| {
                            let summary = Self::get_persistent_summary_for_db(
                                db,
                                &func_ref.summary_cache_key,
                            );
                            if summary.is_none() {
                                info!(
                                    "Summary store has no entry for {}{}",
                                    &func_ref.summary_cache_key, &func_ref.argument_type_key
                                );
                            };
                            summary.unwrap_or_default()
                        })
                }
            }
        }
    }

    /// Returns a summary from the persistent summary cache, preferentially using the concatenation
    /// of persistent_key with arg_types_key as the cache key and falling back to just the
    /// persistent_key if arg_types_key is None.
    #[logfn(TRACE)]
    pub fn get_persistent_summary_using_arg_types_if_possible(
        &self,
        persistent_key: &str,
        arg_types_key: &str,
    ) -> Option<Summary> {
        if !arg_types_key.is_empty() {
            let mut mangled_key = String::new();
            mangled_key.push_str(persistent_key);
            mangled_key.push_str(arg_types_key);
            Self::get_persistent_summary_for_db(&self.db, mangled_key.as_str())
        } else {
            None
        }
    }

    /// Returns the summary corresponding to the persistent_key in the the summary database.
    /// The caller is expected to cache this.
    #[logfn_inputs(TRACE)]
    pub fn get_persistent_summary_for(&self, persistent_key: &str) -> Summary {
        Self::get_persistent_summary_for_db(&self.db, persistent_key).unwrap_or_default()
    }

    /// Helper for get_summary_for and get_persistent_summary_for.
    #[logfn(TRACE)]
    fn get_persistent_summary_for_db(db: &Db, persistent_key: &str) -> Option<Summary> {
        if let Ok(Some(pinned_value)) = db.get(persistent_key.as_bytes()) {
            Some(bincode::deserialize(pinned_value.deref()).unwrap())
        } else {
            None
        }
    }

    /// Sets or updates the typed caches with the call site specialized summary of the
    /// referenced function. Call site specialization involves using the actual generic
    /// arguments supplied by the call site, along with the values of any constant functions
    /// that are supplied as actual arguments.
    #[logfn_inputs(TRACE)]
    pub fn set_summary_for_call_site(
        &mut self,
        func_ref: &Rc<FunctionReference>,
        func_args: &Option<Rc<Vec<Rc<FunctionReference>>>>,
        initial_type_cache: &Option<Rc<HashMap<Rc<Path>, Ty<'tcx>>>>,
        summary: Summary,
    ) {
        if let Some(func_id) = func_ref.function_id {
            if func_args.is_some() || initial_type_cache.is_some() {
                let typed_cache_key =
                    CallSiteKey::new(func_args.clone(), initial_type_cache.clone());
                self.typed_cache_table
                    .entry(typed_cache_key)
                    .or_insert_with(HashMap::new)
                    .insert(func_id, summary);
            } else {
                self.typed_cache.insert(func_id, summary);
            }
        } else {
            //todo: change param to function id
            unreachable!()
        }
    }

    /// Sets or updates the DefId cache so that from now on def_id maps to the given summary.
    #[logfn_inputs(TRACE)]
    pub fn set_summary_for(&mut self, def_id: DefId, summary: Summary) -> Option<Summary> {
        let persistent_key = utils::summary_key_str(self.type_context, def_id);
        let serialized_summary = bincode::serialize(&summary).unwrap();
        let result = self
            .db
            .insert(persistent_key.as_bytes(), serialized_summary);
        if result.is_err() {
            println!("unable to set key in summary database: {:?}", result);
        }
        self.def_id_cache.insert(def_id, summary)
    }
}
