// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::abstract_value;
use crate::abstract_value::AbstractValue;
use crate::abstract_value::AbstractValueTrait;
use crate::expression::Expression;
use crate::path::{Path, PathEnum, PathSelector};

use crate::constant_domain::ConstantDomain;
use log_derive::{logfn, logfn_inputs};
use rpds::HashTrieMap;
use rustc_middle::mir::BasicBlock;
use std::collections::HashSet;
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
    pub fn strong_update_value_at(&mut self, path: Rc<Path>, value: Rc<AbstractValue>) {
        self.value_map.insert_mut(path, value);
    }

    /// Updates the path to value map so that the given path now points to the given value.
    /// Also update any paths that might alias path to now point to a weaker abstract value that
    /// includes all of the concrete values that value might be at runtime.
    #[logfn_inputs(TRACE)]
    pub fn update_value_at(&mut self, path: Rc<Path>, value: Rc<AbstractValue>) {
        self.strong_update_value_at(path.clone(), value.clone());
        self.weakly_update_aliases(path, value, Rc::new(abstract_value::TRUE));
    }

    /// Update any paths that might alias path to now point to a weaker abstract value that
    /// includes all of the concrete values that value might be at runtime.
    #[logfn_inputs(TRACE)]
    fn weakly_update_aliases(
        &mut self,
        path: Rc<Path>,
        value: Rc<AbstractValue>,
        path_condition: Rc<AbstractValue>,
    ) {
        if let Some((condition, true_path, false_path)) = self.try_to_split(&path) {
            // The value path contains an abstract value that was constructed with a conditional.
            // In this case, we split the path into two and perform weak updates on them.
            // Rather than do it here, we recurse until there are no more conditionals.
            self.weakly_update_aliases(
                true_path,
                value.clone(),
                path_condition.and(condition.clone()),
            );
            self.weakly_update_aliases(
                false_path,
                value,
                path_condition.and(condition.logical_not()),
            );
        } else if path_condition.as_bool_if_known().is_none() {
            // If the path condition is true, the value of path will be updated with value
            let old_value = if let Some(v) = self.value_map.get(&path) {
                v.clone()
            } else {
                AbstractValue::make_typed_unknown(value.expression.infer_type(), path.clone())
            };
            // todo: if path contains an abstract value we need to enumerate all possible aliases
            // and weakly update them
            let weak_value = path_condition.conditional_expression(value, old_value);
            self.value_map.insert_mut(path, weak_value);
        }
    }

    /// If the path contains an abstract value that was constructed with a conditional, the path is
    /// concretized into two paths where the abstract value is replaced by the consequent
    /// and alternate, respectively. These paths can then be weakly updated to reflect the
    /// lack of precise knowledge at compile time.
    #[logfn_inputs(TRACE)]
    pub fn try_to_split(
        &mut self,
        path: &Rc<Path>,
    ) -> Option<(Rc<AbstractValue>, Rc<Path>, Rc<Path>)> {
        match &path.value {
            PathEnum::Computed { value } => {
                if let Expression::ConditionalExpression {
                    condition,
                    consequent,
                    alternate,
                } = &value.expression
                {
                    if consequent.might_benefit_from_refinement()
                        && alternate.might_benefit_from_refinement()
                    {
                        return Some((
                            condition.clone(),
                            Path::get_as_path(consequent.refine_with(condition, 0)),
                            Path::get_as_path(alternate.refine_with(&condition.logical_not(), 0)),
                        ));
                    }
                }
                None
            }
            PathEnum::LocalVariable { .. } | PathEnum::Parameter { .. } | PathEnum::Result => {
                self.try_to_split_local(path)
            }
            PathEnum::QualifiedPath {
                ref qualifier,
                ref selector,
                ..
            } => {
                if let Some((condition, true_path, false_path)) = self.try_to_split(qualifier) {
                    let true_path =
                        if let Some(deref_true_path) = Path::try_to_dereference(&true_path, self) {
                            if *selector.as_ref() == PathSelector::Deref {
                                // deref_true_path is now the canonical version of true_path
                                deref_true_path
                            } else {
                                Path::new_qualified(true_path, selector.clone())
                            }
                        } else {
                            Path::new_qualified(true_path, selector.clone())
                        };

                    let false_path = if let Some(deref_false_path) =
                        Path::try_to_dereference(&false_path, self)
                    {
                        if *selector.as_ref() == PathSelector::Deref {
                            // deref_false_path is now the canonical version of false_path
                            deref_false_path
                        } else {
                            Path::new_qualified(false_path, selector.clone())
                        }
                    } else {
                        Path::new_qualified(false_path, selector.clone())
                    };

                    Some((condition, true_path, false_path))
                } else {
                    self.try_to_split_selector(qualifier, selector)
                }
            }
            _ => None,
        }
    }

    /// If the path selector contains an abstract value that was constructed with a conditional, the path is
    /// concretized into two paths where the abstract value is replaced by the consequent
    /// and alternate, respectively. These paths can then be weakly updated to reflect the
    /// lack of precise knowledge at compile time.
    #[logfn_inputs(TRACE)]
    fn try_to_split_selector(
        &mut self,
        qualifier: &Rc<Path>,
        selector: &Rc<PathSelector>,
    ) -> Option<(Rc<AbstractValue>, Rc<Path>, Rc<Path>)> {
        match selector.as_ref() {
            PathSelector::Index(value) => {
                if let Expression::ConditionalExpression {
                    condition,
                    consequent,
                    alternate,
                } = &value.expression
                {
                    if consequent.might_benefit_from_refinement()
                        && alternate.might_benefit_from_refinement()
                    {
                        return Some((
                            condition.clone(),
                            Path::new_index(qualifier.clone(), consequent.clone()),
                            Path::new_index(qualifier.clone(), alternate.clone()),
                        ));
                    }
                }
                None
            }
            PathSelector::Slice(value) => {
                if let Expression::ConditionalExpression {
                    condition,
                    consequent,
                    alternate,
                } = &value.expression
                {
                    if consequent.might_benefit_from_refinement()
                        && alternate.might_benefit_from_refinement()
                    {
                        return Some((
                            condition.clone(),
                            Path::new_slice(qualifier.clone(), consequent.clone()),
                            Path::new_slice(qualifier.clone(), alternate.clone()),
                        ));
                    }
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
        if let Some(AbstractValue {
            expression:
                Expression::ConditionalExpression {
                    condition,
                    consequent,
                    alternate,
                },
            ..
        }) = self.value_at(path).map(Rc::as_ref)
        {
            if let (Expression::HeapBlock { .. }, Expression::HeapBlock { .. })
            | (Expression::Reference(..), Expression::Reference(..)) =
                (&consequent.expression, &alternate.expression)
            {
                Some((
                    condition.clone(),
                    Path::get_as_path(consequent.clone()),
                    Path::get_as_path(alternate.clone()),
                ))
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Returns an environment with a path for every entry in self and other and an associated
    /// value that is condition.conditional_expression(self.value_at(path), other.value_at(path))
    #[logfn_inputs(TRACE)]
    pub fn conditional_join(
        &self,
        other: Environment,
        condition: &Rc<AbstractValue>,
        other_condition: &Rc<AbstractValue>,
    ) -> Environment {
        self.join_or_widen(other, |x, y, _p| {
            if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
                (&x.expression, &y.expression)
            {
                match (v1, v2) {
                    (ConstantDomain::True, ConstantDomain::False) => {
                        return condition.clone();
                    }
                    (ConstantDomain::False, ConstantDomain::True) => {
                        return other_condition.clone();
                    }
                    _ => (),
                }
            }
            condition.conditional_expression(x.clone(), y.clone())
        })
    }

    /// Returns an environment with a path for every entry in self and other and an associated
    /// value that is the join of self.value_at(path) and other.value_at(path)
    #[logfn_inputs(TRACE)]
    pub fn join(&self, other: Environment) -> Environment {
        self.join_or_widen(other, |x, y, p| {
            if let Some(val) = x.get_widened_subexpression(p) {
                return val;
            }
            if let Some(val) = y.get_widened_subexpression(p) {
                return val;
            }
            x.join(y.clone(), p)
        })
    }

    /// Returns an environment with a path for every entry in self and other and an associated
    /// value that is the widen of self.value_at(path) and other.value_at(path)
    #[logfn_inputs(TRACE)]
    pub fn widen(&self, other: Environment) -> Environment {
        self.join_or_widen(other, |x, y, p| {
            if let Some(val) = x.get_widened_subexpression(p) {
                return val;
            }
            if let Some(val) = y.get_widened_subexpression(p) {
                return val;
            }
            x.join(y.clone(), p).widen(p)
        })
    }

    /// Returns a set of paths that do not have identical associated values in both self and other.
    #[logfn_inputs(TRACE)]
    pub fn get_loop_variants(&self, other: &Environment) -> HashSet<Rc<Path>> {
        let mut loop_variants: HashSet<Rc<Path>> = HashSet::new();
        let value_map1 = &self.value_map;
        let value_map2 = &other.value_map;
        for (path, val1) in value_map1.iter() {
            let p = path.clone();
            match value_map2.get(path) {
                Some(val2) => {
                    if !val1.eq(val2) {
                        loop_variants.insert(p);
                    }
                }
                None => {
                    loop_variants.insert(p);
                }
            }
        }
        for (path, _) in value_map2.iter() {
            if !value_map1.contains_key(path) {
                loop_variants.insert(path.clone());
            }
        }
        loop_variants
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
        let mut value_map: HashTrieMap<Rc<Path>, Rc<AbstractValue>> = value_map1.clone();
        for (path, val2) in value_map2.iter() {
            let p = path.clone();
            match value_map1.get(path) {
                Some(val1) => {
                    value_map.insert_mut(p, join_or_widen(val1, val2, path));
                }
                None => {
                    if !path.is_rooted_by_parameter() || val2.is_unit() {
                        // joining bottom and val2
                        // The bottom value corresponds to dead (impossible) code, so the join collapses.
                        value_map.insert_mut(p, val2.clone());
                    } else {
                        let val1 = AbstractValue::make_initial_parameter_value(
                            val2.expression.infer_type(),
                            path.clone(),
                        );
                        value_map.insert_mut(p, join_or_widen(&val1, val2, path));
                    };
                }
            }
        }
        Environment {
            value_map,
            entry_condition: abstract_value::TRUE.into(),
            exit_conditions: HashTrieMap::default(),
        }
    }

    /// Returns true if for every path, self.value_at(path).subset(other.value_at(path))
    #[logfn_inputs(TRACE)]
    pub fn subset(&self, other: &Environment) -> bool {
        let value_map1 = &self.value_map;
        let value_map2 = &other.value_map;
        for (path, val1) in value_map1.iter().filter(|(_, v)| !v.is_bottom()) {
            if let Some(val2) = value_map2.get(path) {
                if !(val1.subset(val2)) {
                    trace!("self at {:?} is {:?} other is {:?}", path, val1, val2);
                    return false;
                }
            }
        }
        true
    }
}
