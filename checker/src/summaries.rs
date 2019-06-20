// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::abstract_value::AbstractValue;
use crate::abstract_value::AbstractValueTrait;
use crate::environment::Environment;
use crate::path::{Path, PathEnum};
use crate::utils;

use rustc::hir::def_id::DefId;
use rustc::ty::TyCtxt;
use rustc_errors::SourceMapper;
use serde::{Deserialize, Serialize};
use sled::Db;
use std::collections::{HashMap, HashSet};
use std::ops::Deref;
use std::rc::Rc;
use syntax_pos;

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
///    sound analysis is only possible one can assume that all such functions have been provided
///    with explicit contract functions.
#[derive(Serialize, Deserialize, Clone, Debug, Default, Eq, PartialEq)]
pub struct Summary {
    /// If true this summary was computed. If false, it is a default summary.
    /// Used to distinguish a computed empty summary from a default summary.
    pub is_not_default: bool,

    // Conditions that should hold prior to the call.
    // Callers should substitute parameter values with argument values and simplify the results
    // under the current path condition. Any values that do not simplify to true will require the
    // caller to either generate an error message or to add a precondition to its own summary that
    // will be sufficient to ensure that all of the preconditions in this summary are met.
    // The string value bundled with the condition is the message that details what would go
    // wrong at runtime if the precondition is not satisfied by the caller.
    pub preconditions: Vec<Precondition>,

    // If the function returns a value, this summarizes what is known statically of the return value.
    // Callers should substitute parameter values with argument values and simplify the result
    // under the current path condition.
    pub result: Option<Rc<AbstractValue>>,

    // Modifications the function makes to mutable state external to the function.
    // Every path will be rooted in a static or in a mutable parameter.
    // No two paths in this collection will lead to the same place in memory.
    // Callers should substitute parameter values with argument values and simplify the results
    // under the current path condition. They should then update their current state to reflect the
    // side-effects of the call.
    pub side_effects: Vec<(Rc<Path>, Rc<AbstractValue>)>,

    // Conditions that should hold subsequent to the call.
    // Callers should substitute parameter values with argument values and simplify the results
    // under the current path condition. The resulting values should be treated as true, so any
    // value that is not the actual value true, should be added to the current path conditions.
    pub post_conditions: Vec<Rc<AbstractValue>>,

    // Condition that if true implies that the call to the function will not complete normally
    // and thus cause the cleanup block of the call to execute (unwinding).
    // Callers should substitute parameter values with argument values and simplify the result
    // under the current path condition. If the simplified value is statically known to be true
    // then the normal destination of the call should be treated as unreachable.
    pub unwind_condition: Option<Rc<AbstractValue>>,

    // Modifications the function makes to mutable state external to the function.
    // Every path will be rooted in a static or in a mutable parameter.
    // No two paths in this collection will lead to the same place in memory.
    // Callers should substitute parameter values with argument values and simplify the results
    // under the current path condition. They should then update their current state to reflect the
    // side-effects of the call for the unwind control paths, following the call.
    pub unwind_side_effects: Vec<(Rc<Path>, Rc<AbstractValue>)>,
}

/// Bundles together the condition of a precondition with the provenance (place where defined) of
/// the condition, along with a diagnostic message to use when the precondition is not (might not be)
/// satisfied.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Precondition {
    /// The condition that must be satisfied when calling a function that has this precondition.
    pub condition: Rc<AbstractValue>,
    /// A diagnostic message to issue if the precondition is not met.
    pub message: Rc<String>,
    /// The source location of the precondition definition (or the source expression/statement that
    /// would panic if the precondition is not met). This is in textual form because it needs to be
    /// persistable and crate independent.
    pub provenance: Option<Rc<String>>,
    /// A stack of source locations that lead to the definition of the precondition (or the source
    /// expression/statement that would panic if the precondition is not met). It is a stack
    /// because the precondition might have been promoted (when a non public function does not meet
    /// a precondition of a function it calls, MIRAI infers a precondition that will allow it to
    /// meet the precondition of the call, so things stack up).
    /// Because this situation arises for non public functions, it is possible to use source spans
    /// rather than strings to track the locations where the promotions happen.
    #[serde(skip)]
    pub spans: Vec<syntax_pos::Span>,
}

/// Constructs a summary of a function body by processing state information gathered during
/// abstract interpretation of the body.
pub fn summarize(
    argument_count: usize,
    exit_environment: &Environment,
    preconditions: &[Precondition],
    post_conditions: &[Rc<AbstractValue>],
    unwind_condition: Option<Rc<AbstractValue>>,
    unwind_environment: &Environment,
    tcx: TyCtxt<'_>,
) -> Summary {
    let mut preconditions: Vec<Precondition> = add_provenance(preconditions, tcx);
    let result = exit_environment.value_at(&Rc::new(PathEnum::LocalVariable { ordinal: 0 }.into()));
    let mut side_effects = extract_side_effects(exit_environment, argument_count);
    let mut post_conditions: Vec<Rc<AbstractValue>> = post_conditions.to_owned();
    let mut unwind_side_effects = extract_side_effects(unwind_environment, argument_count);

    preconditions.sort();
    side_effects.sort();
    post_conditions.sort();
    unwind_side_effects.sort();

    Summary {
        is_not_default: true,
        preconditions,
        result: result.cloned(),
        side_effects,
        post_conditions,
        unwind_condition,
        unwind_side_effects,
    }
}

/// When a precondition is being serialized into a summary, it needs a provenance that is not
/// specific to the current (crate) compilation, since the summary may be used to compile a different
/// crate, or a different version of the current crate.
fn add_provenance(preconditions: &[Precondition], tcx: TyCtxt<'_>) -> Vec<Precondition> {
    let mut result = vec![];
    for precondition in preconditions.iter() {
        let mut precond = precondition.clone();
        if !precondition.spans.is_empty() {
            let span = tcx
                .sess
                .source_map()
                .call_span_if_macro(*precondition.spans.last().unwrap());
            precond.provenance = Some(Rc::new(tcx.sess.source_map().span_to_string(span)));
        }
        result.push(precond);
    }
    result
}

/// When a precondition is used during the compilation of the crate in which it is defined, we
/// want to use the spans, rather than the provenance string (and we don't want to waste memory),
/// so we strip it's provenance string after it has been serialized.
fn remove_provenance(preconditions: &mut Vec<Precondition>) {
    for precondition in preconditions.iter_mut() {
        precondition.provenance = None;
    }
}

/// Returns a list of (path, value) pairs where each path is rooted by an argument(or the result)
/// or where the path root is a heap address reachable from an argument (or the result).
/// Since paths are created by writes, these are side-effects.
/// Since these values are reachable from arguments or the result, they are visible to the caller
/// and must be included in the summary.
fn extract_side_effects(
    env: &Environment,
    argument_count: usize,
) -> Vec<(Rc<Path>, Rc<AbstractValue>)> {
    let mut heap_roots: HashSet<usize> = HashSet::new();
    let mut result = Vec::new();
    for ordinal in 0..=argument_count {
        // remember that 0 is the result
        let root = Rc::new(PathEnum::LocalVariable { ordinal }.into());
        for (path, value) in env
            .value_map
            .iter()
            .filter(|(p, _)| (**p) == root || p.is_rooted_by(&root))
        {
            path.record_heap_addresses(&mut heap_roots);
            value.record_heap_addresses(&mut heap_roots);
            result.push((path.clone(), value.clone()));
        }
    }
    extract_reachable_heap_allocations(env, &mut heap_roots, &mut result);
    result
}

/// Adds roots for all new heap allocated objects that are reachable by the caller.
fn extract_reachable_heap_allocations(
    env: &Environment,
    heap_roots: &mut HashSet<usize>,
    result: &mut Vec<(Rc<Path>, Rc<AbstractValue>)>,
) {
    let mut visited_heap_roots: HashSet<usize> = HashSet::new();
    while heap_roots.len() > visited_heap_roots.len() {
        let mut new_roots: HashSet<usize> = HashSet::new();
        for ordinal in heap_roots.iter() {
            if visited_heap_roots.insert(*ordinal) {
                let root = Rc::new(PathEnum::AbstractHeapAddress { ordinal: *ordinal }.into());
                for (path, value) in env
                    .value_map
                    .iter()
                    .filter(|(p, _)| (**p) == root || p.is_rooted_by(&root))
                {
                    path.record_heap_addresses(&mut new_roots);
                    value.record_heap_addresses(&mut new_roots);
                    result.push((path.clone(), value.clone()));
                }
            }
        }
        heap_roots.extend(new_roots.into_iter());
    }
}

/// A persistent map from summary key to Summary, along with a transient cache from DefId to
/// Summary. The latter is cleared after every outer fixed point loop iteration.
/// Also tracks which definitions depend on (use) any particular Summary.
pub struct PersistentSummaryCache<'a, 'tcx> {
    db: Db,
    cache: HashMap<DefId, Summary>,
    typed_cache: HashMap<usize, Summary>,
    dependencies: HashMap<DefId, Vec<DefId>>,
    key_cache: HashMap<DefId, Rc<String>>,
    type_context: &'a TyCtxt<'tcx>,
}

impl<'a, 'tcx: 'a> PersistentSummaryCache<'a, 'tcx> {
    /// Creates a new persistent summary cache, using (or creating) a Rocks data base at the given
    /// file path.
    pub fn new(
        type_context: &'a TyCtxt<'tcx>,
        summary_store_path: String,
    ) -> PersistentSummaryCache<'a, 'tcx> {
        PersistentSummaryCache {
            db: Db::start_default(summary_store_path)
                .unwrap_or_else(|err| unreachable!(format!("{} ", err))),
            cache: HashMap::new(),
            typed_cache: HashMap::new(),
            key_cache: HashMap::new(),
            dependencies: HashMap::new(),
            type_context,
        }
    }

    /// Any summaries that are still in a default state will be for functions in the foreign_contracts
    /// module and their definitions use DefIds that are different from the ids at the call sites.
    pub fn invalidate_default_summaries(&mut self) {
        let keys_to_remove: Vec<usize> = self
            .typed_cache
            .iter()
            .filter_map(|(id, summary)| {
                if summary.is_not_default {
                    None
                } else {
                    Some(*id)
                }
            })
            .collect();
        for key in keys_to_remove {
            self.typed_cache.remove(&key);
        }
        let keys_to_remove: Vec<DefId> = self
            .cache
            .iter()
            .filter_map(|(def_id, summary)| {
                if summary.is_not_default {
                    None
                } else {
                    Some(*def_id)
                }
            })
            .collect();
        for key in keys_to_remove {
            self.cache.remove(&key);
        }
    }

    /// Returns a list of DefIds for all functions in the current crate that are known
    /// to have used the summary of the function identified by def_id.
    /// Use this after all functions in a crate have been analyzed.
    pub fn get_dependents(&mut self, def_id: &DefId) -> &Vec<DefId> {
        self.dependencies
            .entry(def_id.clone())
            .or_insert_with(Vec::new)
    }

    /// Returns (and caches) a string that uniquely identifies a definition to serve as a key to
    /// the summary cache, which is a key value store. The string will always be the same as
    /// long as the definition does not change its name or location, so it can be used to
    /// transfer information from one compilation to the next, making incremental analysis possible.
    pub fn get_summary_key_for(&mut self, def_id: DefId) -> &Rc<String> {
        let tcx = self.type_context;
        self.key_cache
            .entry(def_id)
            .or_insert_with(|| utils::summary_key_str(tcx, def_id))
    }

    /// Returns the cached summary corresponding to def_id, or creates a default for it.
    /// The optional dependent_def_id is the definition that refers to the returned summary.
    /// The cache tracks all such dependents so that they can be retrieved and re-analyzed
    /// if the cache is updated with a new summary for def_id.
    pub fn get_summary_for(&mut self, def_id: DefId, dependent_def_id: Option<DefId>) -> &Summary {
        match dependent_def_id {
            None => {}
            Some(id) => {
                let dependents = self.dependencies.entry(def_id).or_insert_with(Vec::new);
                if !dependents.contains(&id) {
                    dependents.push(id);
                }
            }
        };
        let db = &self.db;
        let tcx = self.type_context;
        let persistent_key = self
            .key_cache
            .entry(def_id)
            .or_insert_with(|| utils::summary_key_str(tcx, def_id));
        self.cache.entry(def_id).or_insert_with(|| {
            Self::get_persistent_summary_for_db(db, &persistent_key).unwrap_or_default()
        })
    }

    /// Returns the cached summary corresponding to function_id, or creates a default for it.
    /// The optional dependent_def_id is the definition that refers to the returned summary.
    /// The cache tracks all such dependents so that they can be retrieved and re-analyzed
    /// if the cache is updated with a new summary for def_id.
    /// Note that function_id is derived from the location where the function is referenced
    /// and that this location may augment a generic function with type parameter information for,
    /// whereas def_id refers to the generic function itself.
    /// This matters if a useful function summary can only be written for specific generic instantiations.
    pub fn get_summary_for_function_constant(
        &mut self,
        def_id: DefId,
        function_id: usize,
        persistent_key: &str,
        arg_types_key: &str,
        dependent_def_id: DefId,
    ) -> &Summary {
        let dependents = self.dependencies.entry(def_id).or_insert_with(Vec::new);
        if !dependents.contains(&dependent_def_id) {
            dependents.push(dependent_def_id);
        }
        if self.typed_cache.contains_key(&function_id) {
            self.typed_cache.get(&function_id).unwrap()
        } else {
            let db = &self.db;
            if let Some(summary) = Self::get_persistent_summary_using_arg_types_if_possible(
                db,
                persistent_key,
                arg_types_key,
            ) {
                return self.typed_cache.entry(function_id).or_insert(summary);
            }

            // In this case we default to the summary that is not argument type specific, but
            // we need to take care not to cache this summary in self.typed_cache because updating
            // self.cache will not also update self.typed_cache.
            self.cache.entry(def_id).or_insert_with(|| {
                let summary = Self::get_persistent_summary_for_db(db, &persistent_key);
                if !def_id.is_local() && summary.is_none() {
                    info!(
                        "Summary store has no entry for {}{}",
                        persistent_key, arg_types_key
                    );
                };
                summary.unwrap_or_default()
            })
        }
    }

    /// Returns a summary from the persistent summary cache, preferentially using the concatenation
    /// of persistent_key with arg_types_key as the cache key and falling back to just the
    /// persistent_key if arg_types_key is None.
    fn get_persistent_summary_using_arg_types_if_possible(
        db: &Db,
        persistent_key: &str,
        arg_types_key: &str,
    ) -> Option<Summary> {
        if !arg_types_key.is_empty() {
            let mut mangled_key = String::new();
            mangled_key.push_str(persistent_key);
            mangled_key.push_str(arg_types_key);
            Self::get_persistent_summary_for_db(db, mangled_key.as_str())
        } else {
            None
        }
    }

    /// Returns the summary corresponding to the persistent_key in the the summary database.
    /// The caller is expected to cache this.
    pub fn get_persistent_summary_for(&self, persistent_key: &str) -> Summary {
        Self::get_persistent_summary_for_db(&self.db, persistent_key)
            .unwrap_or_else(Summary::default)
    }

    /// Helper for get_summary_for and get_persistent_summary_for.
    fn get_persistent_summary_for_db(db: &Db, persistent_key: &str) -> Option<Summary> {
        if let Ok(Some(pinned_value)) = db.get(persistent_key.as_bytes()) {
            Some(bincode::deserialize(pinned_value.deref()).unwrap())
        } else {
            None
        }
    }

    /// Sets or updates the cache so that from now on def_id maps to the given summary.
    pub fn set_summary_for(&mut self, def_id: DefId, mut summary: Summary) -> Option<Summary> {
        let persistent_key = utils::summary_key_str(self.type_context, def_id);
        let serialized_summary = bincode::serialize(&summary).unwrap();
        let result = self.db.set(persistent_key.as_bytes(), serialized_summary);
        if result.is_err() {
            println!("unable to set key in summary database: {:?}", result);
        }
        // Now that the summary has been serialized we can remove the provenance strings so that
        // we can save memory and better fit in with the normal way of presenting compiler
        // diagnostics.
        remove_provenance(&mut summary.preconditions);
        self.cache.insert(def_id, summary)
    }
}
