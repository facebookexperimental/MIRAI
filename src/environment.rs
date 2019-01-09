// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use abstract_value::{self, AbstractValue, Path};
use rpds::HashTrieMap;
use rustc::hir::def_id::DefId;
use rustc::ty::{self, Ty, TyCtxt};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Environment {
    /// Does not include any entries where the value is abstract_value::Bottom
    value_map: HashTrieMap<Path, AbstractValue>,
}

/// Constructor
impl Environment {
    /// Returns an environment that has a path for every parameter of the given function,
    /// initialized with abstract_values::Top
    pub fn with_parameters(def_id: DefId, tcx: TyCtxt) -> Environment {
        let value_map = HashTrieMap::default();
        let func_ty: Ty = tcx.type_of(def_id);
        match func_ty.sty {
            ty::FnDef(..) | ty::FnPtr(_) => {
                let sig = func_ty.fn_sig(tcx);
                let len = sig.inputs().skip_binder().len();
                for i in 0..len {
                    let par_i = Path::Parameter { index: i };
                    // todo: figure out how to get a source span for each parameter definition
                    value_map.insert(par_i, abstract_value::TOP);
                }
            }
            _ => {}
        };
        Environment { value_map }
    }
}

/// Methods
impl Environment {
    /// Returns a reference to the value associated with the given path.
    /// If no such value exists, &abstract_value::Bottom is returned.
    pub fn value_at(&self, path: &Path) -> &AbstractValue {
        self.value_map.get(path).unwrap_or(&abstract_value::BOTTOM)
    }

    /// Returns an environment with a path for every entry in self and other and an associated
    /// value that is the join of self.value_at(path) and other.value_at(path)
    pub fn join(&self, other: &Environment, join_condition: &AbstractValue) -> Environment {
        self.join_or_widen(other, join_condition, |x, y, c| x.join(y, c))
    }

    /// Returns an environment with a path for every entry in self and other and an associated
    /// value that is the widen of self.value_at(path) and other.value_at(path)
    pub fn widen(&self, other: &Environment, join_condition: &AbstractValue) -> Environment {
        self.join_or_widen(other, join_condition, |x, y, c| x.widen(y, c))
    }

    /// Returns an environment with a path for every entry in self and other and an associated
    /// value that is the join or widen of self.value_at(path) and other.value_at(path).
    fn join_or_widen(
        &self,
        other: &Environment,
        join_condition: &AbstractValue,
        join_or_widen: fn(&AbstractValue, &AbstractValue, &AbstractValue) -> AbstractValue,
    ) -> Environment {
        let value_map1 = &self.value_map;
        let value_map2 = &other.value_map;
        let mut value_map: HashTrieMap<Path, AbstractValue> = HashTrieMap::default();
        for (path, val1) in value_map1.iter() {
            let p = path.clone();
            match value_map2.get(path) {
                Some(val2) => {
                    value_map = value_map.insert(p, join_or_widen(&val1, &val2, &join_condition));
                }
                None => {
                    debug_assert!(!val1.is_bottom());
                    value_map = value_map.insert(
                        p,
                        join_or_widen(&val1, &abstract_value::BOTTOM, &join_condition),
                    );
                }
            }
        }
        for (path, val2) in value_map2.iter() {
            if !value_map1.contains_key(path) {
                debug_assert!(!val2.is_bottom());
                let p = path.clone();
                value_map = value_map.insert(
                    p,
                    join_or_widen(&abstract_value::BOTTOM, &val2, &join_condition),
                );
            }
        }
        Environment { value_map }
    }

    /// Returns true if for every path, self.value_at(path).subset(other.value_at(path))
    pub fn subset(&self, other: &Environment) -> bool {
        let value_map1 = &self.value_map;
        let value_map2 = &other.value_map;
        if value_map1.size() > value_map2.size() {
            // There is a key in value_map1 that has a value that is not bottom and which is not
            // present in value_map2 (and therefore is bottom), hence there is a path where
            // !(self[path] <= other[path])
            return false;
        }
        for (path, val1) in value_map1.iter() {
            match value_map2.get(path) {
                Some(val2) => {
                    if !(val1.subset(val2)) {
                        return false;
                    }
                }
                None => {
                    debug_assert!(!val1.is_bottom());
                    return false;
                }
            }
        }
        true
    }
}
