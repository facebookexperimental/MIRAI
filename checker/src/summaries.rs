// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::abstract_value::AbstractValue;
use crate::abstract_value::AbstractValueTrait;
use crate::environment::Environment;
use crate::path::{Path, PathEnum};
use crate::utils;

use log_derive::{logfn, logfn_inputs};
use rustc::hir::def_id::DefId;
use rustc::ty::TyCtxt;
use rustc_errors::SourceMapper;
use serde::{Deserialize, Serialize};
use sled::{ConfigBuilder, Db};
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Formatter, Result};
use std::fs;
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

    // A condition that should hold subsequent to a call that completes normally.
    // Callers should substitute parameter values with argument values and simplify the results
    // under the current path condition.
    // The resulting value should be conjoined to the current path condition.
    pub post_condition: Option<Rc<AbstractValue>>,

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

impl Summary {
    #[logfn_inputs(TRACE)]
    pub fn is_subset_of(&self, other: &Summary) -> bool {
        if !Self::is_subset_of_preconditions(&self.preconditions[0..], &other.preconditions[0..]) {
            return false;
        }
        if !Self::is_subset_of_result(&self.result, &other.result) {
            return false;
        }
        if !Self::is_subset_of_side_effects(&self.side_effects[0..], &other.side_effects[0..]) {
            return false;
        }
        if !Self::is_subset_of_side_effects(
            &self.unwind_side_effects[0..],
            &other.unwind_side_effects[0..],
        ) {
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
    fn is_subset_of_result(r1: &Option<Rc<AbstractValue>>, r2: &Option<Rc<AbstractValue>>) -> bool {
        match (r1, r2) {
            (Some(v1), Some(v2)) => v1.subset(v2),
            (None, _) => true,
            (_, None) => false,
        }
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

    #[logfn_inputs(TRACE)]
    pub fn widen_with(&self, other: &Summary) -> Summary {
        let side_effects =
            Self::widen_side_effects(&self.side_effects[0..], &other.side_effects[0..], vec![]);
        let unwind_side_effects = Self::widen_side_effects(
            &self.unwind_side_effects[0..],
            &other.unwind_side_effects[0..],
            vec![],
        );
        let result_path = &Rc::new(PathEnum::LocalVariable { ordinal: 0 }.into());
        let result = side_effects
            .iter()
            .find(|&(p, _)| p.eq(result_path))
            .map(|(_, v)| v.clone());

        Summary {
            is_not_default: true,
            preconditions: other.preconditions.clone(),
            result,
            side_effects,
            post_condition: other.post_condition.clone(),
            unwind_condition: None,
            unwind_side_effects,
        }
    }

    #[logfn_inputs(TRACE)]
    fn widen_side_effects(
        e1: &[(Rc<Path>, Rc<AbstractValue>)],
        e2: &[(Rc<Path>, Rc<AbstractValue>)],
        mut acc: Vec<(Rc<Path>, Rc<AbstractValue>)>,
    ) -> Vec<(Rc<Path>, Rc<AbstractValue>)> {
        if e1.is_empty() {
            if e2.is_empty() {
                return acc;
            }
            let (p, v) = &e2[0];
            acc.push((p.clone(), v.widen(p)));
            return Self::widen_side_effects(e1, &e2[1..], acc);
        }
        if e2.is_empty() {
            let (p, v) = &e1[0];
            acc.push((p.clone(), v.widen(p)));
            return Self::widen_side_effects(&e1[1..], e2, acc);
        }
        let (p1, v1) = &e1[0];
        let (p2, v2) = &e2[0];
        if p1 < p2 {
            let (p, v) = &e1[0];
            acc.push((p.clone(), v.widen(p)));
            return Self::widen_side_effects(&e1[1..], e2, acc);
        }
        if p1 > p2 {
            let (p, v) = &e2[0];
            acc.push((p.clone(), v.widen(p)));
            return Self::widen_side_effects(e1, &e2[1..], acc);
        }
        acc.push((p1.clone(), v1.join(v2.clone(), p1).widen(p1)));
        Self::widen_side_effects(&e1[1..], &e2[1..], acc)
    }
}

/// Constructs a summary of a function body by processing state information gathered during
/// abstract interpretation of the body.
#[logfn(TRACE)]
pub fn summarize(
    argument_count: usize,
    exit_environment: &Environment,
    preconditions: &[Precondition],
    post_condition: &Option<Rc<AbstractValue>>,
    unwind_condition: Option<Rc<AbstractValue>>,
    unwind_environment: &Environment,
    tcx: TyCtxt<'_>,
) -> Summary {
    let mut preconditions: Vec<Precondition> = add_provenance(preconditions, tcx);
    let result = exit_environment.value_at(&Rc::new(PathEnum::LocalVariable { ordinal: 0 }.into()));
    let mut side_effects = extract_side_effects(exit_environment, argument_count);
    let mut unwind_side_effects = extract_side_effects(unwind_environment, argument_count);

    preconditions.sort();
    side_effects.sort();
    unwind_side_effects.sort();

    Summary {
        is_not_default: true,
        preconditions,
        result: result.cloned(),
        side_effects,
        post_condition: post_condition.clone(),
        unwind_condition,
        unwind_side_effects,
    }
}

/// When a precondition is being serialized into a summary, it needs a provenance that is not
/// specific to the current (crate) compilation, since the summary may be used to compile a different
/// crate, or a different version of the current crate.
#[logfn(TRACE)]
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
#[logfn_inputs(TRACE)]
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
#[logfn_inputs(TRACE)]
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
#[logfn_inputs(TRACE)]
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

impl<'a, 'tcx> Debug for PersistentSummaryCache<'a, 'tcx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "PersistentSummaryCache".fmt(f)
    }
}

impl<'a, 'tcx: 'a> PersistentSummaryCache<'a, 'tcx> {
    /// Creates a new persistent summary cache, using (or creating) a Sled data base at the given
    /// directory path.
    #[logfn(TRACE)]
    pub fn new(
        type_context: &'a TyCtxt<'tcx>,
        summary_store_directory_str: String,
    ) -> PersistentSummaryCache<'a, 'tcx> {
        use fs2::FileExt;
        use rand::{thread_rng, Rng};
        use std::thread;
        use std::time::Duration;

        let mut rng = thread_rng();
        let summary_store_path =
            Self::create_default_summary_store_if_needed(&summary_store_directory_str);
        let db_path = summary_store_path.join("db");
        let mut options = fs::OpenOptions::new();
        options.create(true);
        options.read(true);
        options.write(true);
        let config_builder = ConfigBuilder::new().path(summary_store_path.clone());
        let config;
        loop {
            match options.open(&db_path) {
                Ok(file) => {
                    if file.try_lock_exclusive().is_ok() {
                        // Give other processes a chance to fail to get the lock and go to sleep.
                        thread::sleep(Duration::from_millis(1));
                        // Have to let the lock go, otherwise config_builder.build() fails.
                        file.unlock().unwrap();
                        // The call to build will still panic if another process intervenes,
                        // but the Sled API provides no way to prevent that.
                        // At this point, however, it is somewhat unlikely.
                        config = config_builder.build();
                        break;
                    }
                    // Fall through to the random sleep interval below.
                }
                Err(..) => {
                    // Probably the file does not yet exist because MIRAI_START_FRESH
                    // has been specified. So just try to create it via config_builder.build().
                    // If there is another reason for failure, it will probably show up in the
                    // panic from build.
                    config = config_builder.build();
                    break;
                }
            }
            let num_millis = rng.gen_range(100, 200);
            thread::sleep(Duration::from_millis(num_millis));
        }
        let db = Db::start(config).unwrap_or_else(|err| unreachable!(format!("{} ", err)));
        PersistentSummaryCache {
            db,
            cache: HashMap::new(),
            typed_cache: HashMap::new(),
            key_cache: HashMap::new(),
            dependencies: HashMap::new(),
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
        if !store_path.exists() && env::var("MIRAI_START_FRESH").is_err() {
            let tar_path = directory_path.join(".summary_store.tar");
            if let Ok(mut f) = File::create(tar_path.clone()) {
                info!("creating a non default new summary store");
                {
                    let bytes = include_bytes!("../../binaries/summary_store.tar");
                    f.write_all(bytes).unwrap();
                }
            }
            let mut ar = Archive::new(File::open(tar_path).unwrap());
            ar.unpack(directory_path).unwrap();
        };
        store_path
    }

    /// Any summaries that are still in a default state will be for functions in the foreign_contracts
    /// module and their definitions use DefIds that are different from the ids at the call sites.
    #[logfn_inputs(TRACE)]
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
    #[logfn_inputs(TRACE)]
    pub fn get_dependents(&mut self, def_id: &DefId) -> &Vec<DefId> {
        self.dependencies
            .entry(def_id.clone())
            .or_insert_with(Vec::new)
    }

    /// Returns (and caches) a string that uniquely identifies a definition to serve as a key to
    /// the summary cache, which is a key value store. The string will always be the same as
    /// long as the definition does not change its name or location, so it can be used to
    /// transfer information from one compilation to the next, making incremental analysis possible.
    #[logfn_inputs(TRACE)]
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
    #[logfn_inputs(TRACE)]
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
    #[logfn_inputs(TRACE)]
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
    #[logfn(TRACE)]
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
    #[logfn_inputs(TRACE)]
    pub fn get_persistent_summary_for(&self, persistent_key: &str) -> Summary {
        Self::get_persistent_summary_for_db(&self.db, persistent_key)
            .unwrap_or_else(Summary::default)
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

    /// Sets or updates the cache so that from now on def_id maps to the given summary.
    #[logfn_inputs(TRACE)]
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
