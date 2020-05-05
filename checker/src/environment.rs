// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::abstract_value;
use crate::abstract_value::AbstractValue;
use crate::abstract_value::AbstractValueTrait;
use crate::expression::Expression;
use crate::path::{Path, PathEnum, PathRefinement};

use log_derive::{logfn, logfn_inputs};
use mirai_annotations::checked_assume;
use rpds::HashTrieMap;
use rustc_middle::mir::BasicBlock;
use std::fmt::{Debug, Formatter, Result};
use std::rc::Rc;

#[derive(Clone, Eq, PartialEq)]
pub struct Environment {
    /// The disjunction of all the exit conditions from the predecessors of this block.
    pub entry_condition: Rc<AbstractValue>,
    /// The conditions that guard exit from this block to successor blocks
    pub exit_conditions: HashTrieMap<BasicBlock, Rc<AbstractValue>>,
    /// Does not include any entries where the value is abstract_value::Bottom
    pub value_map: HashTrieMap<Rc<Path>, Rc<AbstractValue>>,
}

/// Default
impl Environment {
    #[logfn_inputs(TRACE)]
    pub fn default() -> Environment {
        Environment {
            entry_condition: Rc::new(abstract_value::TRUE),
            exit_conditions: HashTrieMap::default(),
            value_map: HashTrieMap::default(),
        }
    }
}

impl Debug for Environment {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_map()
            .entries(self.value_map.iter().map(|(k, v)| (k, v)))
            .finish()
    }
}

/// Methods
impl Environment {
    /// Returns a reference to the value associated with the given path, if there is one.
    #[logfn_inputs(TRACE)]
    #[logfn(TRACE)]
    pub fn value_at(&self, path: &Rc<Path>) -> Option<&Rc<AbstractValue>> {
        self.value_map.get(path)
    }

    /// Updates the path to value map so that the given path now points to the given value.
    #[logfn_inputs(TRACE)]
    pub fn update_value_at(&mut self, path: Rc<Path>, value: Rc<AbstractValue>) {
        if value.is_bottom() || value.is_top() {
            self.value_map = self.value_map.remove(&path);
            return;
        }
        if let Some((join_condition, true_path, false_path)) = self.try_to_split(&path) {
            // If path is an abstraction that can match more than one path, we need to do weak updates.
            let true_val = join_condition.conditional_expression(
                value.clone(),
                self.value_at(&true_path)
                    .unwrap_or(&AbstractValue::make_typed_unknown(
                        value.expression.infer_type(),
                        true_path.clone(),
                    ))
                    .clone(),
            );
            let false_val = join_condition.conditional_expression(
                self.value_at(&false_path)
                    .unwrap_or(&AbstractValue::make_typed_unknown(
                        value.expression.infer_type(),
                        false_path.clone(),
                    ))
                    .clone(),
                value.clone(),
            );
            self.update_value_at(true_path, true_val);
            self.update_value_at(false_path, false_val);
        }
        //todo: if the path contains an Index selector where the index is abstract, then
        //this entry should be weakly updated with any paths that are contained by it and already
        //in the environment.
        //Conversely, if this path is contained in a path that is already in the environment, then
        //that path should be updated weakly.
        self.value_map = self.value_map.insert(path, value);
    }

    /// If the path contains an abstract value that was constructed with a join, the path is
    /// concretized into two paths where the abstract value is replaced by the consequent
    /// and alternate, respectively. These paths can then be weakly updated to reflect the
    /// lack of precise knowledge at compile time.
    #[logfn_inputs(TRACE)]
    fn try_to_split(&mut self, path: &Rc<Path>) -> Option<(Rc<AbstractValue>, Rc<Path>, Rc<Path>)> {
        match &path.value {
            PathEnum::LocalVariable { .. } | PathEnum::Parameter { .. } | PathEnum::Result => {
                self.try_to_split_local(path)
            }
            PathEnum::QualifiedPath {
                ref qualifier,
                ref selector,
                ..
            } => {
                if let Some((join_condition, true_path, false_path)) = self.try_to_split(qualifier)
                {
                    let true_path = Path::new_qualified(true_path, selector.clone());
                    let false_path = Path::new_qualified(false_path, selector.clone());
                    return Some((join_condition, true_path, false_path));
                }
                None
            }
            _ => None,
        }
    }

    /// Helper for try_to_split.
    #[logfn_inputs(TRACE)]
    fn try_to_split_local(
        &mut self,
        path: &Rc<Path>,
    ) -> Option<(Rc<AbstractValue>, Rc<Path>, Rc<Path>)> {
        match self.value_at(path).map(Rc::as_ref) {
            Some(AbstractValue {
                expression:
                    Expression::ConditionalExpression {
                        condition,
                        consequent,
                        alternate,
                    },
                ..
            }) => match (&consequent.expression, &alternate.expression) {
                (Expression::HeapBlock { .. }, Expression::HeapBlock { .. }) => Some((
                    condition.clone(),
                    Path::get_as_path(consequent.clone()),
                    Path::get_as_path(alternate.clone()),
                )),
                (Expression::Reference(path1), Expression::Reference(path2))
                    if path1 != path && path2 != path =>
                {
                    Some((
                        condition.clone(),
                        path1.refine_paths(&self),
                        path2.refine_paths(&self),
                    ))
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Returns an environment with a path for every entry in self and other and an associated
    /// value that is condition.conditional_expression(self.value_at(path), other.value_at(path))
    #[logfn_inputs(TRACE)]
    pub fn conditional_join(
        &self,
        other: Environment,
        condition: &Rc<AbstractValue>,
    ) -> Environment {
        self.join_or_widen(other, |x, y, _| {
            condition.conditional_expression(x.clone(), y.clone())
        })
    }

    /// Returns an environment with a path for every entry in self and other and an associated
    /// value that is the join of self.value_at(path) and other.value_at(path)
    #[logfn_inputs(TRACE)]
    pub fn join(&self, other: Environment) -> Environment {
        self.join_or_widen(other, |x, y, p| x.join(y.clone(), p))
    }

    /// Returns an environment with a path for every entry in self and other and an associated
    /// value that is the widen of self.value_at(path) and other.value_at(path)
    #[logfn_inputs(TRACE)]
    pub fn widen(&self, other: Environment) -> Environment {
        self.clone()
            .join_or_widen(other, |x, y, p| match (&x.expression, &y.expression) {
                (Expression::Widen { .. }, _) => x.clone(),
                (_, Expression::Widen { .. }) => y.clone(),
                _ => x.clone().join(y.clone(), p).widen(p),
            })
    }

    /// Returns an environment with a path for every entry in self and other and an associated
    /// value that is the join or widen of self.value_at(path) and other.value_at(path).
    #[logfn(TRACE)]
    fn join_or_widen<F>(&self, other: Environment, join_or_widen: F) -> Environment
    where
        F: Fn(&Rc<AbstractValue>, &Rc<AbstractValue>, &Rc<Path>) -> Rc<AbstractValue>,
    {
        let value_map1 = &self.value_map;
        let value_map2 = &other.value_map;
        let mut value_map: HashTrieMap<Rc<Path>, Rc<AbstractValue>> = HashTrieMap::default();
        for (path, val1) in value_map1.iter() {
            let p = path.clone();
            match value_map2.get(path) {
                Some(val2) => {
                    value_map = value_map.insert(p, join_or_widen(val1, val2, path));
                }
                None => {
                    checked_assume!(!val1.is_bottom());
                    let val2 = if !path.is_rooted_by_parameter() {
                        val1.clone()
                    } else {
                        AbstractValue::make_from(
                            Expression::Variable {
                                path: path.clone(),
                                var_type: val1.expression.infer_type(),
                            },
                            1,
                        )
                    };
                    value_map = value_map.insert(p, join_or_widen(val1, &val2, path));
                }
            }
        }
        for (path, val2) in value_map2.iter() {
            if !value_map1.contains_key(path) {
                checked_assume!(!val2.is_bottom());
                let val1 = if !path.is_rooted_by_parameter() {
                    val2.clone()
                } else {
                    AbstractValue::make_from(
                        Expression::Variable {
                            path: path.clone(),
                            var_type: val2.expression.infer_type(),
                        },
                        1,
                    )
                };
                value_map = value_map.insert(path.clone(), join_or_widen(&val1, val2, &path));
            }
        }
        Environment {
            value_map,
            entry_condition: Rc::new(abstract_value::TRUE),
            exit_conditions: HashTrieMap::default(),
        }
    }

    /// Returns true if for every path, self.value_at(path).subset(other.value_at(path))
    #[logfn_inputs(TRACE)]
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
