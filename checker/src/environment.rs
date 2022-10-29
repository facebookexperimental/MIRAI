// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::abstract_value;
use crate::abstract_value::AbstractValue;
use crate::abstract_value::AbstractValueTrait;
use crate::expression::{Expression, ExpressionType};
use crate::path::{Path, PathEnum, PathRoot, PathSelector};

use crate::body_visitor::BodyVisitor;
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
impl Default for Environment {
    #[logfn_inputs(TRACE)]
    fn default() -> Environment {
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
    pub fn value_at(&self, path: &Rc<Path>) -> Option<&Rc<AbstractValue>> {
        self.value_map.get(path)
    }

    /// Updates the path to value map so that the given path now points to the given value.
    #[logfn_inputs(TRACE)]
    pub fn strong_update_value_at(&mut self, path: Rc<Path>, value: Rc<AbstractValue>) {
        self.value_map.insert_mut(path, value);
    }

    /// Update any paths that might alias path to now point to a weaker abstract value that
    /// includes all of the concrete values that value might be at runtime.
    #[logfn_inputs(TRACE)]
    pub fn weakly_update_aliases(
        &mut self,
        path: Rc<Path>,
        value: Rc<AbstractValue>,
        path_condition: Rc<AbstractValue>,
        body_visitor: &mut BodyVisitor,
    ) {
        if let Some((condition, true_path, false_path)) = self.try_to_split(&path) {
            // The value path contains an abstract value that was constructed with a conditional.
            // In this case, we split the path into two and perform conditional weak updates on both.
            // Rather than do it here, we recurse until there are no more conditionals.
            self.weakly_update_aliases(
                true_path,
                value.clone(),
                path_condition.and(condition.clone()),
                body_visitor,
            );
            self.weakly_update_aliases(
                false_path,
                value,
                path_condition.and(condition.logical_not()),
                body_visitor,
            );
            return;
        }
        // Incorporate path_condition into value.
        let value = if path_condition.as_bool_if_known().is_none() {
            // If the path condition is true, the value of path will be updated with value, otherwise use:
            let old_value = if let Some(v) = self.value_map.get(&path) {
                v.clone()
            } else {
                AbstractValue::make_typed_unknown(value.expression.infer_type(), path.clone())
            };
            // Combine old with new to get a weakened value
            let weak_value = path_condition.conditional_expression(value, old_value);
            // Do a strong update of path using a weakened value
            self.value_map.insert_mut(path.clone(), weak_value.clone());
            weak_value
        } else {
            value
        };
        // Now look for potential aliases of path that also need updating
        if let PathEnum::QualifiedPath {
            qualifier,
            selector,
            ..
        } = &path.value
        {
            match selector.as_ref() {
                PathSelector::ConstantIndex {
                    offset, from_end, ..
                } => {
                    let mut index = Rc::new((*offset as u128).into());
                    if *from_end {
                        let length_path = Path::new_length(qualifier.clone());
                        let length_val =
                            AbstractValue::make_typed_unknown(ExpressionType::Usize, length_path);
                        index = length_val.subtract(index);
                    };
                    self.weaken_potential_aliased_index_paths(
                        &path,
                        &value,
                        qualifier,
                        &index,
                        body_visitor,
                    )
                }
                PathSelector::Deref => {
                    // we are assigning value to *qualifier and there may be another path *q where
                    // qualifier and q may be the same path at runtime.
                    let value_map = self.value_map.clone();
                    for (p, v) in value_map.iter() {
                        if p.eq(&path) {
                            continue;
                        }
                        if let PathEnum::QualifiedPath {
                            qualifier: qs,
                            selector: s,
                            ..
                        } = &p.value
                        {
                            if **s == PathSelector::Deref {
                                let paths_are_equal = qualifier.equals(qs);
                                match paths_are_equal.as_bool_if_known() {
                                    Some(true) => {
                                        // p is known to be an alias of path, so just update it
                                        self.strong_update_value_at(p.clone(), value.clone());
                                    }
                                    Some(false) => {
                                        // p is known not to be an alias of path
                                        continue;
                                    }
                                    None => {
                                        // p might be an alias of, so weaken its value by making it
                                        // conditional on path_are_equal
                                        let conditional_value = paths_are_equal
                                            .conditional_expression(value.clone(), v.clone());
                                        self.strong_update_value_at(p.clone(), conditional_value);
                                    }
                                }
                            }
                        }
                        if let PathEnum::HeapBlock { .. } = &p.value {
                            let paths_are_equal = qualifier.equals(p);
                            match paths_are_equal.as_bool_if_known() {
                                Some(true) => {
                                    // p is known to be an alias of path, so just update it
                                    self.strong_update_value_at(p.clone(), value.clone());
                                }
                                Some(false) => {
                                    // p is known not to be an alias of path
                                    continue;
                                }
                                None => {
                                    // p might be an alias of, so weaken its value by making it
                                    // conditional on path_are_equal
                                    let conditional_value = paths_are_equal
                                        .conditional_expression(value.clone(), v.clone());
                                    self.strong_update_value_at(p.clone(), conditional_value);
                                }
                            }
                        }
                    }
                }
                PathSelector::Index(index) => self.weaken_potential_aliased_index_paths(
                    &path,
                    &value,
                    qualifier,
                    index,
                    body_visitor,
                ),
                PathSelector::Slice(count) => {
                    // We are assigning value to every element of the slice qualifier[0..count]
                    // There may already be paths for individual elements of the slice.
                    let value_map = self.value_map.clone();
                    for (p, v) in value_map.iter() {
                        if p.eq(&path) {
                            continue;
                        }
                        if let PathEnum::QualifiedPath {
                            qualifier: paq,
                            selector: pas,
                            ..
                        } = &p.value
                        {
                            if paq.ne(qualifier) {
                                // p is not an alias because its qualifier does not match
                                continue;
                            }
                            match pas.as_ref() {
                                PathSelector::ConstantIndex { .. }
                                | PathSelector::ConstantSlice { .. } => {
                                    unreachable!("path {:?} p {:?} v {:?}", path, p, v);
                                }
                                PathSelector::Index(index) => {
                                    // paq[index] might alias an element in qualifier[0..count]
                                    let index_is_in_range = index.less_than(count.clone());
                                    match index_is_in_range.as_bool_if_known() {
                                        Some(true) => {
                                            // p is an alias for sure, so just update it
                                            self.strong_update_value_at(p.clone(), value.clone());
                                        }
                                        Some(false) => {
                                            // p is known not to be an alias
                                            continue;
                                        }
                                        None => {
                                            // p might be an alias, so weaken its value by joining it
                                            // with the slice initializer.
                                            let weakened_value = v.join(value.clone());
                                            // If index is not in range, use the strong value
                                            let guarded_weakened_value = index_is_in_range
                                                .conditional_expression(weakened_value, v.clone());
                                            self.strong_update_value_at(
                                                p.clone(),
                                                guarded_weakened_value,
                                            );
                                        }
                                    }
                                }
                                PathSelector::Slice(c) => {
                                    // The elements of paq[0..c] alias elements of qualifier[0..count]
                                    // If c <= count, then all of the elements of paq[0..c] will be updated with value.
                                    // If c > count, then some of elements will still have value v.
                                    let aliased_slice_is_smaller_or_equal =
                                        c.less_or_equal(count.clone());
                                    let weakened_value = v.join(value.clone());
                                    let guarded_weakened_value = aliased_slice_is_smaller_or_equal
                                        .conditional_expression(value.clone(), weakened_value);
                                    self.strong_update_value_at(p.clone(), guarded_weakened_value);
                                }
                                _ => {}
                            }
                        }
                    }
                }
                PathSelector::ConstantSlice { .. } => {
                    // empty slice, or too large slice, do nothing
                }
                _ => {
                    // we are assigning value to qualifier.selector and there may be another path q.selector where
                    // qualifier and q may be the same path at runtime (and hence should be treated
                    // as a potential alias).
                    let value_map = self.value_map.clone();
                    for (p, v) in value_map.iter() {
                        if p.eq(&path) {
                            continue;
                        }
                        if let PathEnum::QualifiedPath {
                            qualifier: qs,
                            selector: s,
                            ..
                        } = &p.value
                        {
                            if s.eq(selector) {
                                let paths_are_equal = qualifier.equals(qs);
                                match paths_are_equal.as_bool_if_known() {
                                    Some(true) => {
                                        // p is known to be an alias of path, so just update it
                                        self.strong_update_value_at(p.clone(), value.clone());
                                    }
                                    Some(false) => {
                                        // p is known not to be an alias of path
                                        continue;
                                    }
                                    None => {
                                        // p might be an alias of, so weaken its value by making it
                                        // conditional on path_are_equal
                                        let conditional_value = paths_are_equal
                                            .conditional_expression(value.clone(), v.clone());
                                        self.strong_update_value_at(p.clone(), conditional_value);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// We are assigning value to qualifier[index] and there may be other (p[i], v)
    /// pairs in the environment where the runtime location of p[i] might turn out to
    /// be the same as the runtime location of qualifier[index] (i.e. path).
    /// We have to model this uncertainty by weakening v to include the set of
    /// concrete values represented by value.
    fn weaken_potential_aliased_index_paths(
        &mut self,
        path: &Rc<Path>,
        value: &Rc<AbstractValue>,
        qualifier: &Rc<Path>,
        index: &Rc<AbstractValue>,
        body_visitor: &mut BodyVisitor,
    ) {
        let value_map = self.value_map.clone();
        for (p, v) in value_map.iter() {
            check_for_early_return!(body_visitor);
            if p.eq(path) {
                continue;
            }
            if let PathEnum::QualifiedPath {
                qualifier: paq,
                selector: pas,
                ..
            } = &p.value
            {
                if paq.ne(qualifier) {
                    // p is not an alias because its qualifier does not match
                    continue;
                }
                match pas.as_ref() {
                    PathSelector::Index(i) => {
                        // paq[i] might alias an element in qualifier[index]
                        let indices_are_equal = index.equals(i.clone());
                        match indices_are_equal.as_bool_if_known() {
                            Some(true) => {
                                // p is known to be an alias of path, so just update it
                                self.strong_update_value_at(p.clone(), value.clone());
                            }
                            Some(false) => {
                                // p is known not to be an alias of path
                                continue;
                            }
                            None => {
                                // p might be an alias of path, so weaken its value by making it
                                // conditional on index == i
                                let conditional_value = indices_are_equal
                                    .conditional_expression(value.clone(), v.clone());
                                debug!("conditional_value {:?}", conditional_value);
                                self.strong_update_value_at(p.clone(), conditional_value);
                            }
                        }
                    }
                    PathSelector::ConstantIndex { .. }
                    | PathSelector::ConstantSlice { .. }
                    | PathSelector::Slice(..) => {
                        let weakened_value = v.join(value.clone());
                        self.strong_update_value_at(p.clone(), weakened_value);
                    }
                    _ => {}
                }
            }
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
                    return Some((
                        condition.clone(),
                        Path::get_as_path(consequent.refine_with(condition, 0)),
                        Path::get_as_path(alternate.refine_with(&condition.logical_not(), 0)),
                    ));
                }
                None
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
                    return Some((
                        condition.clone(),
                        Path::new_index(qualifier.clone(), consequent.clone()),
                        Path::new_index(qualifier.clone(), alternate.clone()),
                    ));
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
                    return Some((
                        condition.clone(),
                        Path::new_slice(qualifier.clone(), consequent.clone()),
                        Path::new_slice(qualifier.clone(), alternate.clone()),
                    ));
                }
                None
            }
            _ => None,
        }
    }

    /// Returns an environment with a path for every entry in self and other and an associated
    /// value that is condition.conditional_expression(self.value_at(path), other.value_at(path))
    #[logfn_inputs(TRACE)]
    #[must_use]
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
    #[must_use]
    pub fn join(&self, other: Environment) -> Environment {
        self.join_or_widen(other, |x, y, p| {
            if let Some(val) = x.get_widened_subexpression(p) {
                return val;
            }
            if let Some(val) = y.get_widened_subexpression(p) {
                return val;
            }
            x.join(y.clone())
        })
    }

    /// Returns an environment with a path for every entry in self and other and an associated
    /// value that is the widen of self.value_at(path) and other.value_at(path)
    #[logfn_inputs(TRACE)]
    #[must_use]
    pub fn widen(&self, other: Environment) -> Environment {
        self.join_or_widen(other, |x, y, p| {
            if let Some(val) = x.get_widened_subexpression(p) {
                return val;
            }
            if let Some(val) = y.get_widened_subexpression(p) {
                return val;
            }
            if let (
                Expression::WidenedJoin { path: p1, .. },
                Expression::WidenedJoin { path: p2, .. },
            ) = (&x.expression, &y.expression)
            {
                if p1.eq(p2) || p1.eq(p) {
                    return x.clone();
                } else if p2.eq(p) {
                    return y.clone();
                }
            }
            x.join(y.clone()).widen(p)
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
