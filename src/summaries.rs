// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use abstract_value::{AbstractValue, Path};
use environment::Environment;
use rustc::hir::def_id::DefId;
use rustc::ty::TyCtxt;
use std::collections::HashMap;
use std::ops::Deref;

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
#[derive(Serialize, Deserialize, Clone, Debug, Default, Eq, PartialEq, Hash)]
pub struct Summary {
    // Conditions that should hold prior to the call.
    // Callers should substitute parameter values with argument values and simplify the results
    // under the current path condition. Any values that do not simplify to true will require the
    // caller to either generate an error message or to add a precondition to its own summary that
    // will be sufficient to ensure that all of the preconditions in this summary are met.
    // The string value bundled with the condition is the message that details what would go
    // wrong at runtime if the precondition is not satisfied by the caller.
    pub preconditions: Vec<(AbstractValue, String)>,

    // If the function returns a value, this summarizes what is known statically of the return value.
    // Callers should substitute parameter values with argument values and simplify the result
    // under the current path condition.
    pub result: Option<AbstractValue>,

    // Modifications the function makes to mutable state external to the function.
    // Every path will be rooted in a static or in a mutable parameter.
    // No two paths in this collection will lead to the same place in memory.
    // Callers should substitute parameter values with argument values and simplify the results
    // under the current path condition. They should then update their current state to reflect the
    // side-effects of the call.
    pub side_effects: Vec<(Path, AbstractValue)>,

    // Conditions that should hold subsequent to the call.
    // Callers should substitute parameter values with argument values and simplify the results
    // under the current path condition. The resulting values should be treated as true, so any
    // value that is not the actual value true, should be added to the current path conditions.
    pub post_conditions: Vec<AbstractValue>,

    // Condition that if true implies that the call to the function will not complete normally
    // and thus cause the cleanup block of the call to execute (unwinding).
    // Callers should substitute parameter values with argument values and simplify the result
    // under the current path condition. If the simplified value is statically known to be true
    // then the normal destination of the call should be treated as unreachable.
    pub unwind_condition: Option<AbstractValue>,

    // Modifications the function makes to mutable state external to the function.
    // Every path will be rooted in a static or in a mutable parameter.
    // No two paths in this collection will lead to the same place in memory.
    // Callers should substitute parameter values with argument values and simplify the results
    // under the current path condition. They should then update their current state to reflect the
    // side-effects of the call for the unwind control paths, following the call.
    pub unwind_side_effects: Vec<(Path, AbstractValue)>,
}

/// Constructs a summary of a function body by processing state information gathered during
/// abstract interpretation of the body.
pub fn summarize(
    argument_count: usize,
    exit_environment: &Environment,
    preconditions: &[(AbstractValue, String)],
    post_conditions: &[AbstractValue],
    unwind_condition: Option<AbstractValue>,
    unwind_environment: &Environment,
) -> Summary {
    let result = exit_environment.value_at(&Path::LocalVariable { ordinal: 0 });
    let side_effects = extract_side_effects(exit_environment, argument_count);
    let unwind_side_effects = extract_side_effects(unwind_environment, argument_count);
    Summary {
        preconditions: preconditions.to_owned(),
        result: result.cloned(),
        side_effects,
        post_conditions: post_conditions.to_owned(),
        unwind_condition,
        unwind_side_effects,
    }
}

/// Returns a list of (path, value) pairs where each path is rooted by an argument.
/// Since paths are created by writes, these are side-effects when the root is a parameter
/// rather than the return result.
fn extract_side_effects(env: &Environment, argument_count: usize) -> Vec<(Path, AbstractValue)> {
    let mut result = Vec::new();
    for ordinal in 0..=argument_count {
        let root = Path::LocalVariable { ordinal };
        for (path, value) in env
            .value_map
            .iter()
            .filter(|(p, _)| (**p) == root || p.is_rooted_by(&root))
        {
            result.push((path.clone(), value.clone()));
        }
    }
    //todo: what about paths rooted by heap allocated (i.e. boxed) objects that are referenced by
    //the values of the arguments?
    result
}

/// Constructs a string that uniquely identifies a definition to serve as a key to
/// the summary cache, which is a key value store. The string will always be the same as
/// long as the definition does not change its name or location, so it can be used to
/// transfer information from one compilation to the next, making incremental analysis possible.
pub fn summary_key_str(tcx: &TyCtxt, def_id: DefId) -> String {
    let crate_name = if def_id.is_local() {
        tcx.crate_name.as_interned_str().as_str().get()
    } else {
        // This is both ugly and probably brittle, but I can't find any other
        // way to retrieve the crate name from a def_id that is not local.
        // tcx.crate_data_as_rc_any returns an untracked value, which is potentially problematic
        // as per the comments on the function:
        // "Note that this is *untracked* and should only be used within the query
        // system if the result is otherwise tracked through queries"
        // For now, this seems OK since we are only using the crate name.
        // Of course, should a crate name change in an incremental scenario this
        // is going to be the least of our worries.
        let cdata = tcx.crate_data_as_rc_any(def_id.krate);
        let cdata = cdata
            .downcast_ref::<rustc_metadata::cstore::CrateMetadata>()
            .unwrap();
        cdata.name.as_str().get()
    };
    let mut name = String::from(crate_name);
    for component in &tcx.def_path(def_id).data {
        name.push('.');
        let cn = component.data.as_interned_str().as_str().get();
        name.push_str(cn);
        if component.disambiguator != 0 {
            name.push(':');
            let da = component.disambiguator.to_string();
            name.push_str(da.as_str());
        }
    }
    name
}

/// A persistent map from DefId to Summary.
/// Also tracks which definitions depend on (use) any particular Summary.
pub struct PersistentSummaryCache<'a, 'tcx: 'a> {
    db: rocksdb::DB,
    cache: HashMap<DefId, Summary>,
    dependencies: HashMap<DefId, Vec<DefId>>,
    key_cache: HashMap<DefId, String>,
    type_context: &'a TyCtxt<'a, 'tcx, 'tcx>,
}

impl<'a, 'tcx: 'a> PersistentSummaryCache<'a, 'tcx> {
    /// Creates a new persistent summary cache, using (or creating) a Rocks data base at the given
    /// file path.
    pub fn new(
        type_context: &'a TyCtxt<'a, 'tcx, 'tcx>,
        summary_store_path: String,
    ) -> PersistentSummaryCache<'a, 'tcx> {
        PersistentSummaryCache {
            db: rocksdb::DB::open_default(summary_store_path)
                .expect(".summary_store.rocksdb should be a database file"),
            cache: HashMap::new(),
            key_cache: HashMap::new(),
            dependencies: HashMap::new(),
            type_context,
        }
    }

    pub fn get_summary_key_for(&mut self, def_id: DefId) -> &String {
        let tcx = self.type_context;
        self.key_cache
            .entry(def_id)
            .or_insert_with(|| summary_key_str(tcx, def_id))
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
                if dependents.contains(&id) {
                    dependents.push(id);
                }
            }
        };
        let tcx = self.type_context;
        let db = &self.db;
        self.cache.entry(def_id).or_insert_with(|| {
            let persistent_key = summary_key_str(tcx, def_id);
            Self::get_persistent_summary_for_db(db, &persistent_key)
        })
    }

    /// Returns the summary corresponding to the persistent_key in the the summary database.
    /// The caller is expected to cache this.
    pub fn get_persistent_summary_for(&self, persistent_key: &str) -> Summary {
        let db = &self.db;
        Self::get_persistent_summary_for_db(db, persistent_key)
    }

    /// Helper for get_summary_for and get_persistent_summary_for.
    fn get_persistent_summary_for_db(db: &rocksdb::DB, persistent_key: &str) -> Summary {
        match db.get(persistent_key.as_bytes()) {
            Ok(Some(serialized_summary)) => {
                bincode::deserialize(serialized_summary.deref()).unwrap()
            }
            _ => Summary::default(), // todo: #33 look for a contract summary or construct from type
        }
    }

    /// Sets or updates the cache so that from now on def_id maps to summary.
    /// Returns a list of DefIds that need to be re-analyzed because they used
    /// the previous summary corresponding to def_id.
    /// This operation amounts to an expensive no-op if the summary is identical to the
    /// one that is already in the cache. Avoiding this is the caller's responsibility.
    pub fn set_summary_for(&mut self, def_id: DefId, summary: Summary) -> &Vec<DefId> {
        let persistent_key = summary_key_str(self.type_context, def_id);
        let serialized_summary = bincode::serialize(&summary).unwrap();
        self.db
            .put(persistent_key.as_bytes(), &serialized_summary)
            .unwrap();
        self.cache.insert(def_id, summary);
        self.dependencies.entry(def_id).or_insert_with(Vec::new)
    }
}
