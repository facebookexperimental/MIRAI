// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::abstract_domains::AbstractDomain;
use crate::abstract_value::{self, AbstractValue, Path};
use crate::expression::Expression;

use log::debug;
use mirai_annotations::checked_assume;
use rpds::HashTrieMap;
use rustc::mir::BasicBlock;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter, Result};

#[derive(Clone, Eq, PartialEq)]
pub struct Environment {
    /// The disjunction of all the exit conditions from the predecessors of this block.
    pub entry_condition: AbstractValue,
    /// The conditions that guard exit from this block to successor blocks
    pub exit_conditions: HashMap<BasicBlock, AbstractValue>,
    /// Does not include any entries where the value is abstract_value::Bottom
    pub value_map: HashTrieMap<Path, AbstractValue>,
}

/// Default
impl Environment {
    pub fn default() -> Environment {
        Environment {
            entry_condition: abstract_value::TRUE,
            exit_conditions: HashMap::default(),
            value_map: HashTrieMap::default(),
        }
    }
}

impl Debug for Environment {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.value_map.fmt(f)
    }
}

/// Methods
impl Environment {
    /// Returns a reference to the value associated with the given path, if there is one.
    pub fn value_at(&self, path: &Path) -> Option<&AbstractValue> {
        self.value_map.get(path)
    }

    /// Updates the path to value map so that the given path now points to the given value.
    pub fn update_value_at(&mut self, path: Path, value: AbstractValue) {
        debug!("updating value of {:?} to {:?}", path, value);
        if value.is_bottom() {
            self.value_map = self.value_map.remove(&path);
            return;
        }
        if let Some((join_condition, true_path, false_path)) = self.try_to_split(&path) {
            // If path is an abstraction that can match more than one path, we need to do weak updates.
            let top = abstract_value::TOP;
            let true_val = value.join(self.value_at(&true_path).unwrap_or(&top), &join_condition);;
            let false_val = self
                .value_at(&false_path)
                .unwrap_or(&top)
                .join(&value, &join_condition);
            self.update_value_at(true_path, true_val);
            self.update_value_at(false_path, false_val);
        }
        self.value_map = self.value_map.insert(path, value);
    }

    /// If the path contains an abstract value that was constructed with a join, the path is
    /// concretized into two paths where the abstract value is replaced by the consequent
    /// and alternate, respectively. These paths can then be weakly updated to reflect the
    /// lack of precise knowledge at compile time.
    fn try_to_split(&mut self, path: &Path) -> Option<(AbstractValue, Path, Path)> {
        match path {
            Path::LocalVariable { .. } => self.try_to_split_local(path),
            Path::QualifiedPath {
                ref qualifier,
                ref selector,
                ..
            } => {
                if let Some((join_condition, true_path, false_path)) = self.try_to_split(qualifier)
                {
                    let true_path = Path::QualifiedPath {
                        length: true_path.path_length() + 1,
                        qualifier: box true_path,
                        selector: selector.clone(),
                    };
                    let false_path = Path::QualifiedPath {
                        length: false_path.path_length() + 1,
                        qualifier: box false_path,
                        selector: selector.clone(),
                    };
                    return Some((join_condition, true_path, false_path));
                }
                None
            }
            _ => None,
        }
    }

    /// Helper for try_to_split.
    fn try_to_split_local(&mut self, path: &Path) -> Option<(AbstractValue, Path, Path)> {
        let val_opt = self.value_at(path);
        if let Some(val) = val_opt {
            if let AbstractValue {
                domain:
                    AbstractDomain {
                        expression:
                            Expression::ConditionalExpression {
                                condition,
                                consequent,
                                alternate,
                            },
                        ..
                    },
                provenance,
            } = val
            {
                match (&consequent.expression, &alternate.expression) {
                    (
                        Expression::AbstractHeapAddress(addr1),
                        Expression::AbstractHeapAddress(addr2),
                    ) => {
                        return Some((
                            AbstractValue {
                                provenance: provenance.clone(),
                                domain: (**condition).clone(),
                            },
                            Path::AbstractHeapAddress { ordinal: *addr1 },
                            Path::AbstractHeapAddress { ordinal: *addr2 },
                        ));
                    }
                    (Expression::Reference(path1), Expression::Reference(path2)) => {
                        return Some((
                            AbstractValue {
                                provenance: provenance.clone(),
                                domain: (**condition).clone(),
                            },
                            path1.clone(),
                            path2.clone(),
                        ));
                    }
                    _ => (),
                }
            }
        };
        None
    }

    /// Returns an environment with a path for every entry in self and other and an associated
    /// value that is the join of self.value_at(path) and other.value_at(path)
    pub fn join(&self, other: &Environment, join_condition: &AbstractValue) -> Environment {
        self.join_or_widen(other, join_condition, |x, y, c, _p| x.join(y, c))
    }

    /// Returns an environment with a path for every entry in self and other and an associated
    /// value that is the widen of self.value_at(path) and other.value_at(path)
    pub fn widen(&self, other: &Environment, join_condition: &AbstractValue) -> Environment {
        self.join_or_widen(other, join_condition, |x, y, c, p| x.widen(y, c, p))
    }

    /// Returns an environment with a path for every entry in self and other and an associated
    /// value that is the join or widen of self.value_at(path) and other.value_at(path).
    fn join_or_widen(
        &self,
        other: &Environment,
        join_condition: &AbstractValue,
        join_or_widen: fn(&AbstractValue, &AbstractValue, &AbstractValue, &Path) -> AbstractValue,
    ) -> Environment {
        let value_map1 = &self.value_map;
        let value_map2 = &other.value_map;
        let mut value_map: HashTrieMap<Path, AbstractValue> = HashTrieMap::default();
        for (path, val1) in value_map1.iter() {
            let p = path.clone();
            match value_map2.get(path) {
                Some(val2) => {
                    value_map =
                        value_map.insert(p, join_or_widen(&val1, &val2, &join_condition, path));
                }
                None => {
                    checked_assume!(!val1.is_bottom());
                    let val = join_or_widen(&val1, &abstract_value::BOTTOM, &join_condition, path);
                    if !val.is_bottom() {
                        value_map = value_map.insert(p, val);
                    }
                }
            }
        }
        for (path, val2) in value_map2.iter() {
            if !value_map1.contains_key(path) {
                checked_assume!(!val2.is_bottom());
                let p = path.clone();
                let val = join_or_widen(&abstract_value::BOTTOM, &val2, &join_condition, path);
                if !val.is_bottom() {
                    value_map = value_map.insert(p, val);
                }
            }
        }
        Environment {
            value_map,
            entry_condition: abstract_value::TRUE,
            exit_conditions: HashMap::default(),
        }
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
                    checked_assume!(!val1.is_bottom());
                    return false;
                }
            }
        }
        true
    }
}
