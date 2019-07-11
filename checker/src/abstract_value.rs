// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

#![allow(clippy::declare_interior_mutable_const)]
use crate::constant_domain::ConstantDomain;
use crate::environment::Environment;
use crate::expression::Expression::{ConditionalExpression, Join, Widen};
use crate::expression::{Expression, ExpressionType};
use crate::interval_domain::{self, IntervalDomain};
use crate::k_limits;
use crate::path::PathRefinement;
use crate::path::{Path, PathEnum};

use log_derive::{logfn, logfn_inputs};
use serde::{Deserialize, Serialize};
use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt::{Debug, Formatter, Result};
use std::hash::Hash;
use std::hash::Hasher;
use std::rc::Rc;

// See https://github.com/facebookexperimental/MIRAI/blob/master/documentation/AbstractValues.md.

/// Mirai is an abstract interpreter and thus produces abstract values.
/// In general, an abstract value is a value that is not fully known.
/// For example, we may know that it is a number between 1 and 10, but not
/// which particular number.
///
/// When we do know everything about a value, it is concrete rather than
/// abstract, but is convenient to just use this structure for concrete values
/// as well, since all operations can be uniform.
#[derive(Serialize, Deserialize, Clone, Eq, Ord, PartialOrd)]
pub struct AbstractValue {
    // This is not a domain element, but a representation of how this value has been constructed.
    // It is used to refine the value with respect to path conditions and actual arguments.
    // It is also used to construct corresponding domain elements, when needed.
    pub expression: Expression,
    // Keeps track of how large the expression is.
    // When an expression gets too large it needs to get widened otherwise execution time diverges.
    pub expression_size: u64,
    /// Cached interval domain element computed on demand by get_as_interval.
    #[serde(skip)]
    interval: RefCell<Option<Rc<IntervalDomain>>>,
}

impl Debug for AbstractValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.expression.fmt(f)
    }
}

impl Hash for AbstractValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.expression.hash(state);
    }
}

impl PartialEq for AbstractValue {
    #[logfn_inputs(TRACE)]
    fn eq(&self, other: &Self) -> bool {
        match (&self.expression, &other.expression) {
            (Expression::Widen { path: p1, .. }, Expression::Widen { path: p2, .. }) => p1.eq(p2),
            (e1, e2) => e1.eq(e2),
        }
    }
}

/// An abstract domain element that all represent the impossible concrete value.
/// I.e. the corresponding set of possible concrete values is empty.
pub const BOTTOM: AbstractValue = AbstractValue {
    expression: Expression::Bottom,
    expression_size: 1,
    interval: RefCell::new(None),
};

/// An abstract domain element that all represent the single concrete value, false.
pub const FALSE: AbstractValue = AbstractValue {
    expression: Expression::CompileTimeConstant(ConstantDomain::False),
    expression_size: 1,
    interval: RefCell::new(None),
};

/// An abstract domain element that all represents all possible concrete values.
pub const TOP: AbstractValue = AbstractValue {
    expression: Expression::Top,
    expression_size: 1,
    interval: RefCell::new(None),
};

/// An abstract domain element that all represent the single concrete value, true.
pub const TRUE: AbstractValue = AbstractValue {
    expression: Expression::CompileTimeConstant(ConstantDomain::True),
    expression_size: 1,
    interval: RefCell::new(None),
};

impl From<bool> for AbstractValue {
    #[logfn_inputs(TRACE)]
    fn from(b: bool) -> AbstractValue {
        if b {
            AbstractValue {
                expression: Expression::CompileTimeConstant(ConstantDomain::True),
                expression_size: 1,
                interval: RefCell::new(None),
            }
        } else {
            AbstractValue {
                expression: Expression::CompileTimeConstant(ConstantDomain::False),
                expression_size: 1,
                interval: RefCell::new(None),
            }
        }
    }
}

impl From<ConstantDomain> for AbstractValue {
    #[logfn_inputs(TRACE)]
    fn from(cv: ConstantDomain) -> AbstractValue {
        AbstractValue {
            expression: Expression::CompileTimeConstant(cv),
            expression_size: 1,
            interval: RefCell::new(None),
        }
    }
}

impl AbstractValue {
    /// Creates an abstract value from a binary expression and keeps track of the size.
    #[logfn_inputs(TRACE)]
    fn make_binary(
        left: Rc<AbstractValue>,
        right: Rc<AbstractValue>,
        operation: fn(Rc<AbstractValue>, Rc<AbstractValue>) -> Expression,
    ) -> Rc<AbstractValue> {
        let expression_size = left.expression_size.saturating_add(right.expression_size);
        Self::make_from(operation(left, right), expression_size)
    }

    /// Creates an abstract value from a typed binary expression and keeps track of the size.
    #[logfn_inputs(TRACE)]
    fn make_typed_binary(
        left: Rc<AbstractValue>,
        right: Rc<AbstractValue>,
        result_type: ExpressionType,
        operation: fn(Rc<AbstractValue>, Rc<AbstractValue>, ExpressionType) -> Expression,
    ) -> Rc<AbstractValue> {
        let expression_size = left.expression_size.saturating_add(right.expression_size);
        Self::make_from(operation(left, right, result_type), expression_size)
    }

    /// Creates an abstract value from a typed unary expression and keeps track of the size.
    #[logfn_inputs(TRACE)]
    fn make_typed_unary(
        operand: Rc<AbstractValue>,
        result_type: ExpressionType,
        operation: fn(Rc<AbstractValue>, ExpressionType) -> Expression,
    ) -> Rc<AbstractValue> {
        let expression_size = operand.expression_size.saturating_add(1);
        Self::make_from(operation(operand, result_type), expression_size)
    }

    /// Creates an abstract value from a unary expression and keeps track of the size.
    #[logfn_inputs(TRACE)]
    fn make_unary(
        operand: Rc<AbstractValue>,
        operation: fn(Rc<AbstractValue>) -> Expression,
    ) -> Rc<AbstractValue> {
        let expression_size = operand.expression_size.saturating_add(1);
        Self::make_from(operation(operand), expression_size)
    }

    /// Creates an abstract value from the given expression and size.
    /// Initializes the optional domains to None.
    #[logfn_inputs(TRACE)]
    pub fn make_from(expression: Expression, expression_size: u64) -> Rc<AbstractValue> {
        if expression_size > k_limits::MAX_EXPRESSION_SIZE {
            return Rc::new(TOP);
        }
        Rc::new(AbstractValue {
            expression,
            expression_size,
            interval: RefCell::new(None),
        })
    }
}

pub trait AbstractValueTrait: Sized {
    fn addition(&self, other: Self) -> Self;
    fn add_equalities_for_widened_vars(
        &self,
        self_env: &Environment,
        widened_env: &Environment,
    ) -> Self;
    fn add_overflows(&self, other: Self, target_type: ExpressionType) -> Self;
    fn and(&self, other: Self) -> Self;
    fn as_bool_if_known(&self) -> Option<bool>;
    fn as_int_if_known(&self) -> Option<Rc<AbstractValue>>;
    fn bit_and(&self, other: Self) -> Self;
    fn bit_or(&self, other: Self) -> Self;
    fn bit_xor(&self, other: Self) -> Self;
    fn cast(&self, target_type: ExpressionType) -> Self;
    fn conditional_expression(&self, consequent: Self, alternate: Self) -> Self;
    fn divide(&self, other: Self) -> Self;
    fn equals(&self, other: Self) -> Self;
    fn greater_or_equal(&self, other: Self) -> Self;
    fn greater_than(&self, other: Self) -> Self;
    fn implies(&self, other: &Self) -> bool;
    fn implies_not(&self, other: &Self) -> bool;
    fn inverse_implies_not(&self, other: &Rc<AbstractValue>) -> bool;
    fn is_bottom(&self) -> bool;
    fn is_top(&self) -> bool;
    fn join(&self, other: Self, path: &Rc<Path>) -> Self;
    fn less_or_equal(&self, other: Self) -> Self;
    fn less_than(&self, other: Self) -> Self;
    fn multiply(&self, other: Self) -> Self;
    fn mul_overflows(&self, other: Self, target_type: ExpressionType) -> Self;
    fn negate(self) -> Self;
    fn not_equals(&self, other: Self) -> Self;
    fn logical_not(&self) -> Self;
    fn offset(&self, other: Self) -> Self;
    fn or(&self, other: Self) -> Self;
    fn record_heap_addresses(&self, result: &mut HashSet<usize>);
    fn remainder(&self, other: Self) -> Self;
    fn shift_left(&self, other: Self) -> Self;
    fn shl_overflows(&self, other: Self, target_type: ExpressionType) -> Self;
    fn shr(&self, other: Self, expression_type: ExpressionType) -> Self;
    fn shr_overflows(&self, other: Self, target_type: ExpressionType) -> Self;
    fn subtract(&self, other: Self) -> Self;
    fn sub_overflows(&self, other: Self, target_type: ExpressionType) -> Self;
    fn subset(&self, other: &Self) -> bool;
    fn try_to_simplify_binary_op(
        &self,
        other: Self,
        const_op: fn(&ConstantDomain, &ConstantDomain) -> ConstantDomain,
        operation: fn(Self, Self) -> Self,
    ) -> Self;
    fn try_to_distribute_binary_op(&self, other: Self, operation: fn(Self, Self) -> Self) -> Self;
    fn get_cached_interval(&self) -> Rc<IntervalDomain>;
    fn get_as_interval(&self) -> IntervalDomain;
    fn refine_paths(&self, environment: &Environment) -> Self;
    fn refine_parameters(&self, arguments: &[(Rc<Path>, Rc<AbstractValue>)], fresh: usize) -> Self;
    fn refine_with(&self, path_condition: &Self, depth: usize) -> Self;
    fn widen(&self, path: &Rc<Path>) -> Self;
}

impl AbstractValueTrait for Rc<AbstractValue> {
    /// Returns an element that is "self + other".
    #[logfn_inputs(TRACE)]
    fn addition(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        if let Expression::Add { left, right } = &self.expression {
            if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
                (&right.expression, &other.expression)
            {
                let folded = v1.add(v2);
                if folded != ConstantDomain::Bottom {
                    return left.addition(Rc::new(folded.into()));
                }
            }
        }
        self.try_to_simplify_binary_op(other, ConstantDomain::add, |l, r| {
            AbstractValue::make_binary(l, r, |left, right| Expression::Add { left, right })
        })
    }

    /// Returns an expression that is self && equalities where the latter term is constructed
    /// from the values of the self_env for keys that are in the widened_env and have values
    /// that have been widened. This prevents a true self condition from collapsing the path
    /// condition at a join point.
    #[logfn_inputs(TRACE)]
    fn add_equalities_for_widened_vars(
        &self,
        self_env: &Environment,
        widened_env: &Environment,
    ) -> Rc<AbstractValue> {
        let mut result = self.clone();
        for (key, val) in widened_env.value_map.iter() {
            if let Expression::Widen { .. } = val.expression {
                if let Some(self_val) = self_env.value_map.get(key) {
                    if let Expression::Widen { .. } = self_val.expression {
                        continue;
                    };
                    let var_type = self_val.expression.infer_type();
                    if !var_type.is_primitive() {
                        continue;
                    }
                    let variable = AbstractValue::make_from(
                        Expression::Variable {
                            path: key.clone(),
                            var_type,
                        },
                        1,
                    );
                    let equality =
                        AbstractValue::make_binary(variable, self_val.clone(), |left, right| {
                            Expression::Equals { left, right }
                        });
                    result = result.and(equality);
                }
            }
        }
        result
    }

    /// Returns an element that is true if "self + other" is not in range of target_type.
    #[logfn_inputs(TRACE)]
    fn add_overflows(
        &self,
        other: Rc<AbstractValue>,
        target_type: ExpressionType,
    ) -> Rc<AbstractValue> {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.add_overflows(v2, &target_type);
            if result != ConstantDomain::Bottom {
                return Rc::new(result.into());
            }
        };
        let interval = self.get_cached_interval().add(&other.get_cached_interval());
        if interval.is_contained_in(&target_type) {
            return Rc::new(FALSE);
        }
        AbstractValue::make_typed_binary(
            self.clone(),
            other,
            target_type,
            |left, right, result_type| Expression::AddOverflows {
                left,
                right,
                result_type,
            },
        )
    }

    /// Returns an element that is "self && other".
    #[logfn_inputs(TRACE)]
    fn and(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        let self_bool = self.as_bool_if_known();
        if let Some(false) = self_bool {
            return Rc::new(FALSE);
        };
        let other_bool = other.as_bool_if_known();
        if let Some(false) = other_bool {
            return Rc::new(FALSE);
        };
        if self_bool.unwrap_or(false) {
            if other_bool.unwrap_or(false) {
                Rc::new(TRUE)
            } else {
                other
            }
        } else if other_bool.unwrap_or(false)
            || self.is_top()
            || self.is_bottom() && other.is_bottom()
        {
            self.clone()
        } else if other.is_top() {
            other
        } else {
            // todo: #32 more simplifications
            AbstractValue::make_binary(self.clone(), other, |left, right| Expression::And {
                left,
                right,
            })
        }
    }

    /// The Boolean value of this expression, if known, otherwise None.
    #[logfn_inputs(TRACE)]
    fn as_bool_if_known(&self) -> Option<bool> {
        match self.expression {
            Expression::CompileTimeConstant(ConstantDomain::True) => Some(true),
            Expression::CompileTimeConstant(ConstantDomain::False) => Some(false),
            _ => {
                // todo: ask other domains about this (construct some if need be).
                None
            }
        }
    }

    /// If the concrete Boolean value of this abstract value is known, return it as a UI28 constant,
    /// otherwise return None.
    #[logfn_inputs(TRACE)]
    fn as_int_if_known(&self) -> Option<Rc<AbstractValue>> {
        self.as_bool_if_known()
            .map(|b| Rc::new(ConstantDomain::U128(b as u128).into()))
    }

    /// Returns an element that is "self & other".
    #[logfn_inputs(TRACE)]
    fn bit_and(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.bit_and(v2);
            if result != ConstantDomain::Bottom {
                return Rc::new(result.into());
            }
        };
        AbstractValue::make_binary(self.clone(), other, |left, right| Expression::BitAnd {
            left,
            right,
        })
    }

    /// Returns an element that is "self | other".
    #[logfn_inputs(TRACE)]
    fn bit_or(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.bit_or(v2);
            if result != ConstantDomain::Bottom {
                return Rc::new(result.into());
            }
        };
        AbstractValue::make_binary(self.clone(), other, |left, right| Expression::BitOr {
            left,
            right,
        })
    }

    /// Returns an element that is "self ^ other".
    #[logfn_inputs(TRACE)]
    fn bit_xor(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.bit_xor(v2);
            if result != ConstantDomain::Bottom {
                return Rc::new(result.into());
            }
        };
        AbstractValue::make_binary(self.clone(), other, |left, right| Expression::BitXor {
            left,
            right,
        })
    }

    /// Returns an element that is "self as target_type".
    #[logfn_inputs(TRACE)]
    fn cast(&self, target_type: ExpressionType) -> Rc<AbstractValue> {
        if let Expression::CompileTimeConstant(v1) = &self.expression {
            let result = v1.cast(&target_type);
            if result != ConstantDomain::Bottom {
                return Rc::new(result.into());
            }
        };
        match &self.expression {
            Expression::Bottom => self.clone(),
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => condition.conditional_expression(
                consequent.cast(target_type.clone()),
                alternate.cast(target_type),
            ),
            Expression::Join { left, right, path } => left
                .cast(target_type.clone())
                .join(right.cast(target_type), &path),
            _ => AbstractValue::make_typed_unary(
                self.clone(),
                target_type,
                |operand, target_type| Expression::Cast {
                    operand,
                    target_type,
                },
            ),
        }
    }

    /// Returns an element that is "if self { consequent } else { alternate }".
    #[logfn_inputs(TRACE)]
    fn conditional_expression(
        &self,
        consequent: Rc<AbstractValue>,
        alternate: Rc<AbstractValue>,
    ) -> Rc<AbstractValue> {
        if self.is_bottom() {
            // If the condition is impossible so is the expression.
            return consequent;
        }
        if consequent.expression == alternate.expression {
            // c ? x : x is just x
            return consequent;
        }
        let join_condition_as_bool = self.as_bool_if_known();
        if join_condition_as_bool == Some(true) {
            // true ? x : y is just x
            return consequent;
        } else if join_condition_as_bool == Some(false) {
            // false ? x : y is just y
            return alternate;
        }
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&consequent.expression, &alternate.expression)
        {
            match (v1, v2) {
                (ConstantDomain::True, ConstantDomain::False) => {
                    // c ? true : false is just c
                    return self.clone();
                }
                (ConstantDomain::False, ConstantDomain::True) => {
                    // c ? false : true is just !c
                    return self.logical_not();
                }
                _ => (),
            }
        }
        let expression_size = self
            .expression_size
            .saturating_add(consequent.expression_size)
            .saturating_add(alternate.expression_size);
        AbstractValue::make_from(
            ConditionalExpression {
                condition: self.clone(),
                consequent,
                alternate,
            },
            expression_size,
        )
    }

    /// Returns an element that is "self / other".
    #[logfn_inputs(TRACE)]
    fn divide(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        self.try_to_simplify_binary_op(other, ConstantDomain::div, |l, r| {
            AbstractValue::make_binary(l, r, |left, right| Expression::Div { left, right })
        })
    }

    /// Returns an element that is "self == other".
    #[logfn_inputs(TRACE)]
    fn equals(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            return Rc::new(v1.equals(v2).into());
        };
        match (&self.expression, &other.expression) {
            // If self and other are the same location in memory, return true unless the value might be NaN.
            (
                Expression::Variable {
                    path: p1,
                    var_type: t1,
                },
                Expression::Variable {
                    path: p2,
                    var_type: t2,
                },
            ) => {
                if p1 == p2 {
                    match (t1, t2) {
                        (ExpressionType::F32, _)
                        | (ExpressionType::F64, _)
                        | (_, ExpressionType::F32)
                        | (_, ExpressionType::F64) => (),
                        _ => {
                            return Rc::new(TRUE);
                        }
                    }
                }
            }
            // (c ? 0 : 1) == 0 is the same as c
            // (c ? 1 : 0) == 1 is the same as c
            // (c ? 0 : 1) == 1 is the same as !c
            // (c ? 1 : 0) == 0 is the same as !c
            (
                Expression::ConditionalExpression {
                    condition,
                    consequent,
                    alternate,
                },
                Expression::CompileTimeConstant(ConstantDomain::U128(result_val)),
            ) => {
                if let (
                    Expression::CompileTimeConstant(ConstantDomain::U128(cons_val)),
                    Expression::CompileTimeConstant(ConstantDomain::U128(alt_val)),
                ) = (&consequent.expression, &alternate.expression)
                {
                    match (*cons_val, *alt_val, *result_val) {
                        (0, 1, 0) | (1, 0, 1) => {
                            return condition.clone();
                        }
                        (0, 1, 1) | (1, 0, 0) => {
                            return condition.logical_not();
                        }
                        _ => (),
                    }
                }
            }
            // !x == 0 is the same as x when x is Boolean. Canonicalize it to the latter.
            (
                Expression::Not { operand },
                Expression::CompileTimeConstant(ConstantDomain::U128(val)),
            ) => {
                if *val == 0 && operand.expression.infer_type() == ExpressionType::Bool {
                    return operand.clone();
                }
            }
            // x == 0 is the same as !x when x is a Boolean. Canonicalize it to the latter.
            // x == 1 is the same as x when x is a Boolean. Canonicalize it to the latter.
            (x, Expression::CompileTimeConstant(ConstantDomain::U128(val))) => {
                if x.infer_type() == ExpressionType::Bool {
                    if *val == 0 {
                        return self.logical_not();
                    } else if *val == 1 {
                        return self.clone();
                    }
                }
            }
            (x, y) => {
                // If self and other are the same expression and the expression could not result in NaN
                // and the expression represents exactly one value, we can simplify this to true.
                if x == y && !x.infer_type().is_floating_point_number() {
                    return Rc::new(TRUE);
                }
            }
        }
        // Return an equals expression rather than a constant expression.
        AbstractValue::make_binary(self.clone(), other, |left, right| Expression::Equals {
            left,
            right,
        })
    }

    /// Returns an element that is "self >= other".
    #[logfn_inputs(TRACE)]
    fn greater_or_equal(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            return Rc::new(v1.greater_or_equal(v2).into());
        };
        if let Some(result) = self
            .get_cached_interval()
            .greater_or_equal(&other.get_cached_interval())
        {
            return Rc::new(result.into());
        }
        AbstractValue::make_binary(self.clone(), other, |left, right| {
            Expression::GreaterOrEqual { left, right }
        })
    }

    /// Returns an element that is "self > other".
    #[logfn_inputs(TRACE)]
    fn greater_than(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            return Rc::new(v1.greater_than(v2).into());
        };
        if let Some(result) = self
            .get_cached_interval()
            .greater_than(other.get_cached_interval().as_ref())
        {
            return Rc::new(result.into());
        }
        AbstractValue::make_binary(self.clone(), other, |left, right| Expression::GreaterThan {
            left,
            right,
        })
    }

    /// Returns true if "self => other" is known at compile time to be true.
    /// Returning false does not imply the implication is false, just that we do not know.
    #[logfn_inputs(TRACE)]
    fn implies(&self, other: &Rc<AbstractValue>) -> bool {
        // x => true, is always true
        // false => x, is always true
        // x => x, is always true
        if other.as_bool_if_known().unwrap_or(false)
            || !self.as_bool_if_known().unwrap_or(true)
            || self.eq(other)
        {
            return true;
        }

        // x && y => x
        // y && x => x
        if let Expression::And { left, right } = &self.expression {
            return left.implies(other) || right.implies(other);
        }
        false
    }

    /// Returns true if "self => !other" is known at compile time to be true.
    /// Returning false does not imply the implication is false, just that we do not know.
    #[logfn_inputs(TRACE)]
    fn implies_not(&self, other: &Rc<AbstractValue>) -> bool {
        // x => !false, is always true
        // false => !x, is always true
        if !other.as_bool_if_known().unwrap_or(true) || !self.as_bool_if_known().unwrap_or(true) {
            return true;
        };
        // !x => !x
        if let Expression::Not { ref operand } = self.expression {
            return (**operand).eq(other);
        }
        false
    }

    /// Returns true if "!self => !other" is known at compile time to be true.
    /// Returning false does not imply the implication is false, just that we do not know.
    #[logfn_inputs(TRACE)]
    fn inverse_implies_not(&self, other: &Rc<AbstractValue>) -> bool {
        if self == other {
            return true;
        }
        if let Expression::And { left, right } = &other.expression {
            return self.inverse_implies_not(left) || self.implies_not(right);
        }
        false
    }

    /// True if the set of concrete values that correspond to this domain is empty.
    #[logfn_inputs(TRACE)]
    fn is_bottom(&self) -> bool {
        match self.expression {
            Expression::Bottom => true,
            _ => false,
        }
    }

    /// True if all possible concrete values are elements of the set corresponding to this domain.
    #[logfn_inputs(TRACE)]
    fn is_top(&self) -> bool {
        match self.expression {
            Expression::Top => true,
            _ => false,
        }
    }

    /// Returns a domain whose corresponding set of concrete values include all of the values
    /// corresponding to self and other. In effect this behaves like set union.
    #[logfn_inputs(TRACE)]
    fn join(&self, other: Rc<AbstractValue>, path: &Rc<Path>) -> Rc<AbstractValue> {
        // {} union y is just y
        if self.is_bottom() {
            return other;
        }
        // x union {} is just x
        if other.is_bottom() {
            return self.clone();
        }
        // x union x is just x
        if (*self) == other {
            return other;
        }
        // widened(x) union y is just widened(x)
        if let Expression::Widen { .. } = &self.expression {
            return self.clone();
        }
        // x union widened(y) is just widened(y)
        if let Expression::Widen { .. } = &other.expression {
            return other.clone();
        }
        let expression_size = self.expression_size.saturating_add(other.expression_size);
        AbstractValue::make_from(
            Expression::Join {
                path: path.clone(),
                left: self.clone(),
                right: other,
            },
            expression_size,
        )
    }

    /// Returns an element that is "self <= other".
    #[logfn_inputs(TRACE)]
    fn less_or_equal(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            return Rc::new(v1.less_or_equal(v2).into());
        };
        if let Some(result) = self
            .get_cached_interval()
            .less_equal(&other.get_cached_interval())
        {
            return Rc::new(result.into());
        }
        AbstractValue::make_binary(self.clone(), other, |left, right| Expression::LessOrEqual {
            left,
            right,
        })
    }

    /// Returns an element that is self < other
    #[logfn_inputs(TRACE)]
    fn less_than(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            return Rc::new(v1.less_than(v2).into());
        };
        if let Some(result) = self
            .get_cached_interval()
            .less_than(other.get_cached_interval().as_ref())
        {
            return Rc::new(result.into());
        }
        AbstractValue::make_binary(self.clone(), other, |left, right| Expression::LessThan {
            left,
            right,
        })
    }

    /// Returns an element that is "self * other".
    #[logfn_inputs(TRACE)]
    fn multiply(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        self.try_to_simplify_binary_op(other, ConstantDomain::mul, |l, r| {
            AbstractValue::make_binary(l, r, |left, right| Expression::Mul { left, right })
        })
    }

    /// Returns an element that is true if "self * other" is not in range of target_type.
    #[logfn_inputs(TRACE)]
    fn mul_overflows(
        &self,
        other: Rc<AbstractValue>,
        target_type: ExpressionType,
    ) -> Rc<AbstractValue> {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.mul_overflows(v2, &target_type);
            if result != ConstantDomain::Bottom {
                return Rc::new(result.into());
            }
        };
        let interval = self.get_cached_interval().mul(&other.get_cached_interval());
        if interval.is_contained_in(&target_type) {
            return Rc::new(FALSE);
        }
        AbstractValue::make_typed_binary(
            self.clone(),
            other,
            target_type,
            |left, right, result_type| Expression::MulOverflows {
                left,
                right,
                result_type,
            },
        )
    }

    /// Returns an element that is "-self".
    #[logfn_inputs(TRACE)]
    fn negate(self) -> Rc<AbstractValue> {
        if let Expression::CompileTimeConstant(v1) = &self.expression {
            let result = v1.neg();
            if result != ConstantDomain::Bottom {
                return Rc::new(result.into());
            }
        };
        AbstractValue::make_unary(self.clone(), |operand| Expression::Neg { operand })
    }

    /// Returns an element that is "self != other".
    #[logfn_inputs(TRACE)]
    fn not_equals(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            return Rc::new(v1.not_equals(v2).into());
        };
        AbstractValue::make_binary(self.clone(), other, |left, right| Expression::Ne {
            left,
            right,
        })
    }

    /// Returns an element that is "!self".
    #[logfn_inputs(TRACE)]
    fn logical_not(&self) -> Rc<AbstractValue> {
        if let Expression::CompileTimeConstant(v1) = &self.expression {
            let result = v1.not();
            if result != ConstantDomain::Bottom {
                return Rc::new(result.into());
            }
        };
        match &self.expression {
            Expression::Bottom => self.clone(),
            Expression::Not { operand } => operand.clone(),
            _ => AbstractValue::make_unary(self.clone(), |operand| Expression::Not { operand }),
        }
    }

    /// Returns an element that is "self.other".
    #[logfn_inputs(TRACE)]
    fn offset(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        AbstractValue::make_binary(self.clone(), other, |left, right| Expression::Offset {
            left,
            right,
        })
    }

    /// Returns an element that is "self || other".
    #[logfn_inputs(TRACE)]
    fn or(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        fn unsimplified(x: &Rc<AbstractValue>, y: Rc<AbstractValue>) -> Rc<AbstractValue> {
            AbstractValue::make_binary(x.clone(), y, |left, right| Expression::Or { left, right })
        }
        if self.as_bool_if_known().unwrap_or(false) || other.as_bool_if_known().unwrap_or(false) {
            Rc::new(TRUE)
        } else if self.is_bottom() || !self.as_bool_if_known().unwrap_or(true) {
            other
        } else if other.is_bottom() || !other.as_bool_if_known().unwrap_or(true) {
            self.clone()
        } else {
            // x |\ x = x
            if self.expression == other.expression {
                return other;
            }
            // (!x || x) = true
            if let Expression::Not { operand } = &self.expression {
                if operand.eq(&other) {
                    return Rc::new(TRUE);
                }
            }
            // (x || (x && y)) = x, etc.
            if self.inverse_implies_not(&other) {
                return self.clone();
            }
            match (&self.expression, &other.expression) {
                (Expression::Not { ref operand }, _) if (**operand).eq(&other) => Rc::new(TRUE),
                (_, Expression::Not { ref operand }) if (**operand).eq(&self) => Rc::new(TRUE),
                //(x && y) || (x && !y) = x
                (
                    Expression::And {
                        left: x1,
                        right: y1,
                    },
                    Expression::And {
                        left: x2,
                        right: y2,
                    },
                ) if x1 == x2 && y1.logical_not().eq(y2) => x1.clone(),
                // (((c ? e : 1) == 1) || ((c ? e : 1) == 0)) = !c || e == 0 || e == 1
                (
                    Expression::Equals {
                        left: l1,
                        right: r1,
                    },
                    Expression::Equals {
                        left: l2,
                        right: r2,
                    },
                ) if l1 == l2 && r1.expression.is_one() && r2.expression.is_zero() => {
                    if let Expression::ConditionalExpression {
                        condition: c,
                        consequent: e,
                        alternate: one,
                    } = &l1.expression
                    {
                        if one.expression.is_one() {
                            let not_c = c.logical_not();
                            let e_eq_0 = e.equals(Rc::new(ConstantDomain::U128(0).into()));
                            let e_eq_1 = e.equals(Rc::new(ConstantDomain::U128(1).into()));
                            return not_c.or(e_eq_0).or(e_eq_1);
                        }
                    }
                    unsimplified(self, other)
                }
                _ => unsimplified(self, other),
            }
        }
    }

    /// Adds any abstract heap addresses found in the associated expression to the given set.
    #[logfn_inputs(TRACE)]
    fn record_heap_addresses(&self, result: &mut HashSet<usize>) {
        self.expression.record_heap_addresses(result);
    }

    /// Returns an element that is "self % other".
    #[logfn_inputs(TRACE)]
    fn remainder(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        self.try_to_simplify_binary_op(other, ConstantDomain::rem, |l, r| {
            AbstractValue::make_binary(l, r, |left, right| Expression::Rem { left, right })
        })
    }

    /// Returns an element that is "self << other".
    #[logfn_inputs(TRACE)]
    fn shift_left(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.shl(v2);
            if result != ConstantDomain::Bottom {
                return Rc::new(result.into());
            }
        };
        AbstractValue::make_binary(self.clone(), other, |left, right| Expression::Shl {
            left,
            right,
        })
    }

    /// Returns an element that is true if "self << other" shifts away all bits.
    #[logfn_inputs(TRACE)]
    fn shl_overflows(
        &self,
        other: Rc<AbstractValue>,
        target_type: ExpressionType,
    ) -> Rc<AbstractValue> {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.shl_overflows(v2, &target_type);
            if result != ConstantDomain::Bottom {
                return Rc::new(result.into());
            }
        };
        let interval = other.get_cached_interval();
        if interval.is_contained_in_width_of(&target_type) {
            return Rc::new(FALSE);
        }
        AbstractValue::make_typed_binary(
            self.clone(),
            other,
            target_type,
            |left, right, result_type| Expression::ShlOverflows {
                left,
                right,
                result_type,
            },
        )
    }

    /// Returns an element that is "self >> other".
    #[logfn_inputs(TRACE)]
    fn shr(&self, other: Rc<AbstractValue>, expression_type: ExpressionType) -> Rc<AbstractValue> {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.shr(v2);
            if result != ConstantDomain::Bottom {
                return Rc::new(result.into());
            }
        };
        AbstractValue::make_typed_binary(
            self.clone(),
            other,
            expression_type,
            |left, right, result_type| Expression::Shr {
                left,
                right,
                result_type,
            },
        )
    }

    /// Returns an element that is true if "self >> other" shifts away all bits.
    #[logfn_inputs(TRACE)]
    fn shr_overflows(
        &self,
        other: Rc<AbstractValue>,
        target_type: ExpressionType,
    ) -> Rc<AbstractValue> {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.shr_overflows(v2, &target_type);
            if result != ConstantDomain::Bottom {
                return Rc::new(result.into());
            }
        };
        let interval = &other.get_cached_interval();
        if interval.is_contained_in_width_of(&target_type) {
            return Rc::new(FALSE);
        }
        AbstractValue::make_typed_binary(
            self.clone(),
            other,
            target_type,
            |left, right, result_type| Expression::ShrOverflows {
                left,
                right,
                result_type,
            },
        )
    }

    /// Returns an element that is "self - other".
    #[logfn_inputs(TRACE)]
    fn subtract(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        self.try_to_simplify_binary_op(other, ConstantDomain::sub, |l, r| {
            AbstractValue::make_binary(l, r, |left, right| Expression::Sub { left, right })
        })
    }

    /// Returns an element that is true if "self - other" is not in range of target_type.
    #[logfn_inputs(TRACE)]
    fn sub_overflows(
        &self,
        other: Rc<AbstractValue>,
        target_type: ExpressionType,
    ) -> Rc<AbstractValue> {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.sub_overflows(v2, &target_type);
            if result != ConstantDomain::Bottom {
                return Rc::new(result.into());
            }
        };
        let interval = self.get_cached_interval().sub(&other.get_cached_interval());
        if interval.is_contained_in(&target_type) {
            return Rc::new(FALSE);
        }
        AbstractValue::make_typed_binary(
            self.clone(),
            other,
            target_type,
            |left, right, result_type| Expression::SubOverflows {
                left,
                right,
                result_type,
            },
        )
    }

    /// True if all of the concrete values that correspond to self also correspond to other.
    /// Note: !x.subset(y) does not imply y.subset(x).
    #[logfn_inputs(TRACE)]
    fn subset(&self, other: &Rc<AbstractValue>) -> bool {
        if self == other {
            return true;
        };
        match (&self.expression, &other.expression) {
            // The empty set is a subset of every other set.
            (Expression::Bottom, _) => true,
            // A non empty set is not a subset of the empty set.
            (_, Expression::Bottom) => false,
            // Every set is a subset of the universal set.
            (_, Expression::Top) => true,
            // The universal set is not a subset of any set other than the universal set.
            (Expression::Top, _) => false,
            // Widened expressions are equal if their paths are equal, regardless of their operand values.
            (Expression::Widen { path: p1, .. }, Expression::Widen { path: p2, .. }) => p1 == p2,
            // (condition ? consequent : alternate) is a subset of x if both consequent and alternate are subsets of x.
            (
                Expression::ConditionalExpression {
                    consequent,
                    alternate,
                    ..
                },
                _,
            ) => {
                // This is a conservative answer. False does not imply other.subset(self).
                consequent.subset(other) && alternate.subset(other)
            }
            // x is a subset of (condition ? consequent : alternate) if x is a subset of consequent or alternate.
            (
                _,
                Expression::ConditionalExpression {
                    consequent,
                    alternate,
                    ..
                },
            ) => {
                // This is a conservative answer. False does not imply other.subset(self).
                self.subset(&consequent) || self.subset(&alternate)
            }
            // x subset widen { z } if x subset z
            (_, Expression::Widen { operand, .. }) => self.subset(&operand),
            // (left join right) is a subset of x if both left and right are subsets of x.
            (Expression::Join { left, right, .. }, _) => {
                // This is a conservative answer. False does not imply other.subset(self).
                left.subset(other) && right.subset(other)
            }
            // x is a subset of (left join right) if x is a subset of either left or right.
            (_, Expression::Join { left, right, .. }) => {
                // This is a conservative answer. False does not imply other.subset(self).
                self.subset(&left) || self.subset(&right)
            }
            // in all other cases we conservatively answer false
            _ => false,
        }
    }

    /// Tries to simplify operation(self, other) by constant folding or by distribution
    /// the operation over self and/or other.
    /// Returns operation(self, other) if no simplification is possible.
    #[logfn(TRACE)]
    fn try_to_simplify_binary_op(
        &self,
        other: Rc<AbstractValue>,
        const_op: fn(&ConstantDomain, &ConstantDomain) -> ConstantDomain,
        operation: fn(Rc<AbstractValue>, Rc<AbstractValue>) -> Rc<AbstractValue>,
    ) -> Rc<AbstractValue> {
        match (&self.expression, &other.expression) {
            (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) => {
                let result = const_op(v1, v2);
                if result == ConstantDomain::Bottom {
                    self.try_to_distribute_binary_op(other, operation)
                } else {
                    Rc::new(result.into())
                }
            }
            _ => self.try_to_distribute_binary_op(other, operation),
        }
    }

    /// Tries to distribute the operation over self and/or other.
    /// Return operation(self, other) if no simplification is possible.
    #[logfn_inputs(TRACE)]
    fn try_to_distribute_binary_op(
        &self,
        other: Rc<AbstractValue>,
        operation: fn(Rc<AbstractValue>, Rc<AbstractValue>) -> Rc<AbstractValue>,
    ) -> Rc<AbstractValue> {
        if let ConditionalExpression {
            condition,
            consequent,
            alternate,
        } = &self.expression
        {
            return condition.conditional_expression(
                operation(consequent.clone(), other.clone()),
                operation(alternate.clone(), other.clone()),
            );
        };
        if let ConditionalExpression {
            condition,
            consequent,
            alternate,
        } = &other.expression
        {
            return condition.conditional_expression(
                operation(self.clone(), consequent.clone()),
                operation(self.clone(), alternate.clone()),
            );
        };
        if let Join { left, right, path } = &self.expression {
            return operation(left.clone(), other.clone())
                .join(operation(right.clone(), other), &path);
        }
        if let Join { left, right, path } = &other.expression {
            return operation(self.clone(), left.clone())
                .join(operation(self.clone(), right.clone()), &path);
        }
        match (&self.expression, &other.expression) {
            (Widen { .. }, _) => self.clone(),
            (_, Widen { .. }) => other,
            _ => operation(self.clone(), other),
        }
    }

    /// Gets or constructs an interval that is cached.
    #[logfn_inputs(TRACE)]
    fn get_cached_interval(&self) -> Rc<IntervalDomain> {
        {
            let mut cache = self.interval.borrow_mut();
            if cache.is_some() {
                return cache.as_ref().unwrap().clone();
            }
            let interval = self.get_as_interval();
            *cache = Some(Rc::new(interval));
        }
        self.get_cached_interval()
    }

    /// Constructs an element of the Interval domain for simple expressions.
    #[logfn_inputs(TRACE)]
    fn get_as_interval(&self) -> IntervalDomain {
        match &self.expression {
            Expression::Top => interval_domain::BOTTOM,
            Expression::Add { left, right } => left.get_as_interval().add(&right.get_as_interval()),
            Expression::CompileTimeConstant(ConstantDomain::I128(val)) => (*val).into(),
            Expression::CompileTimeConstant(ConstantDomain::U128(val)) => (*val).into(),
            Expression::ConditionalExpression {
                consequent,
                alternate,
                ..
            } => consequent
                .get_as_interval()
                .widen(&alternate.get_as_interval()),
            Expression::Join { left, right, .. } => {
                left.get_as_interval().widen(&right.get_as_interval())
            }
            Expression::Mul { left, right } => left.get_as_interval().mul(&right.get_as_interval()),
            Expression::Neg { operand } => operand.get_as_interval().neg(),
            Expression::Sub { left, right } => left.get_as_interval().sub(&right.get_as_interval()),
            Expression::Variable { .. } => interval_domain::BOTTOM,
            Expression::Widen { operand, .. } => {
                let interval = operand.get_as_interval();
                if interval.is_bottom() {
                    return interval;
                }
                if let Expression::Join { left, .. } = &operand.expression {
                    let left_interval = left.get_as_interval();
                    if left_interval.is_bottom() {
                        return interval_domain::BOTTOM;
                    }
                    match (left_interval.lower_bound(), interval.lower_bound()) {
                        (Some(llb), Some(lb)) if llb == lb => {
                            // The lower bound is finite and does not change as a result of the fixed
                            // point computation, so we can keep it, but we remove the upper bound.
                            return interval.remove_upper_bound();
                        }
                        _ => (),
                    }
                    match (left_interval.upper_bound(), interval.upper_bound()) {
                        (Some(lub), Some(ub)) if lub == ub => {
                            // The upper bound is finite and does not change as a result of the fixed
                            // point computation, so we can keep it, but we remove the lower bound.
                            return interval.remove_lower_bound();
                        }
                        _ => (),
                    }
                }
                interval
            }
            _ => interval_domain::BOTTOM,
        }
    }

    /// Replaces occurrences of Expression::Variable(path) with the value at that path
    /// in the given environment (if there is such a value).
    #[logfn_inputs(TRACE)]
    fn refine_paths(&self, environment: &Environment) -> Rc<AbstractValue> {
        match &self.expression {
            Expression::Top | Expression::Bottom | Expression::AbstractHeapAddress(..) => {
                self.clone()
            }
            Expression::Add { left, right } => left
                .refine_paths(environment)
                .addition(right.refine_paths(environment)),
            Expression::AddOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_paths(environment)
                .add_overflows(right.refine_paths(environment), result_type.clone()),
            Expression::And { left, right } => left
                .refine_paths(environment)
                .and(right.refine_paths(environment)),
            Expression::BitAnd { left, right } => left
                .refine_paths(environment)
                .bit_and(right.refine_paths(environment)),
            Expression::BitOr { left, right } => left
                .refine_paths(environment)
                .bit_or(right.refine_paths(environment)),
            Expression::BitXor { left, right } => left
                .refine_paths(environment)
                .bit_xor(right.refine_paths(environment)),
            Expression::Cast {
                operand,
                target_type,
            } => operand.refine_paths(environment).cast(target_type.clone()),
            Expression::CompileTimeConstant(..) => self.clone(),
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => condition.refine_paths(environment).conditional_expression(
                consequent.refine_paths(environment),
                alternate.refine_paths(environment),
            ),
            Expression::Div { left, right } => left
                .refine_paths(environment)
                .divide(right.refine_paths(environment)),
            Expression::Equals { left, right } => left
                .refine_paths(environment)
                .equals(right.refine_paths(environment)),
            Expression::GreaterOrEqual { left, right } => left
                .refine_paths(environment)
                .greater_or_equal(right.refine_paths(environment)),
            Expression::GreaterThan { left, right } => left
                .refine_paths(environment)
                .greater_than(right.refine_paths(environment)),
            Expression::Join { left, right, path } => left
                .refine_paths(environment)
                .join(right.refine_paths(environment), &path),
            Expression::LessOrEqual { left, right } => left
                .refine_paths(environment)
                .less_or_equal(right.refine_paths(environment)),
            Expression::LessThan { left, right } => left
                .refine_paths(environment)
                .less_than(right.refine_paths(environment)),
            Expression::Mul { left, right } => left
                .refine_paths(environment)
                .multiply(right.refine_paths(environment)),
            Expression::MulOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_paths(environment)
                .mul_overflows(right.refine_paths(environment), result_type.clone()),
            Expression::Ne { left, right } => left
                .refine_paths(environment)
                .not_equals(right.refine_paths(environment)),
            Expression::Neg { operand } => operand.refine_paths(environment).negate(),
            Expression::Not { operand } => operand.refine_paths(environment).logical_not(),
            Expression::Offset { left, right } => left
                .refine_paths(environment)
                .offset(right.refine_paths(environment)),
            Expression::Or { left, right } => left
                .refine_paths(environment)
                .or(right.refine_paths(environment)),
            Expression::Reference(path) => {
                let refined_path = path.refine_paths(environment);
                AbstractValue::make_from(Expression::Reference(refined_path), 1)
            }
            Expression::Rem { left, right } => left
                .refine_paths(environment)
                .remainder(right.refine_paths(environment)),
            Expression::Shl { left, right } => left
                .refine_paths(environment)
                .shift_left(right.refine_paths(environment)),
            Expression::ShlOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_paths(environment)
                .shl_overflows(right.refine_paths(environment), result_type.clone()),
            Expression::Shr {
                left,
                right,
                result_type,
            } => left
                .refine_paths(environment)
                .shr(right.refine_paths(environment), result_type.clone()),
            Expression::ShrOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_paths(environment)
                .shr_overflows(right.refine_paths(environment), result_type.clone()),
            Expression::Sub { left, right } => left
                .refine_paths(environment)
                .subtract(right.refine_paths(environment)),
            Expression::SubOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_paths(environment)
                .sub_overflows(right.refine_paths(environment), result_type.clone()),
            Expression::UnknownModelField { path, default } => {
                if let Some(val) = environment.value_at(&path) {
                    // This environment has a value for the model field.
                    val.clone()
                } else if let PathEnum::QualifiedPath { qualifier, .. } = &path.value {
                    if environment.value_at(&*qualifier).is_some() {
                        // This environment does have a value for the qualifier, so the buck stops here.
                        default.clone()
                    } else {
                        // Keep passing the buck to the next caller.
                        AbstractValue::make_from(
                            Expression::UnknownModelField {
                                path: path.clone(),
                                default: default.clone(),
                            },
                            default.expression_size.saturating_add(1),
                        )
                    }
                } else {
                    unreachable!()
                }
            }
            Expression::Variable { path, var_type } => {
                if let Some(val) = environment.value_at(&path) {
                    val.clone()
                } else {
                    let refined_path = path.refine_paths(environment);
                    if let PathEnum::Constant { value } = &refined_path.value {
                        value.clone()
                    } else if let Some(val) = environment.value_at(&refined_path) {
                        val.clone()
                    } else {
                        AbstractValue::make_from(
                            Expression::Variable {
                                path: refined_path,
                                var_type: var_type.clone(),
                            },
                            1,
                        )
                    }
                }
            }
            Expression::Widen { path, operand } => operand
                .refine_paths(environment)
                .widen(&path.refine_paths(environment)),
        }
    }

    /// Returns a value that is simplified (refined) by replacing parameter values
    /// with their corresponding argument values. If no refinement is possible
    /// the result is simply a clone of this value.
    #[logfn_inputs(TRACE)]
    fn refine_parameters(
        &self,
        arguments: &[(Rc<Path>, Rc<AbstractValue>)],
        // An offset to add to locals from the called function so that they do not clash with caller locals.
        fresh: usize,
    ) -> Rc<AbstractValue> {
        match &self.expression {
            Expression::Top | Expression::Bottom => self.clone(),
            Expression::AbstractHeapAddress(ordinal) => {
                AbstractValue::make_from(Expression::AbstractHeapAddress(*ordinal + fresh), 1)
            }
            Expression::Add { left, right } => left
                .refine_parameters(arguments, fresh)
                .addition(right.refine_parameters(arguments, fresh)),
            Expression::AddOverflows {
                left,
                right,
                result_type,
            } => left.refine_parameters(arguments, fresh).add_overflows(
                right.refine_parameters(arguments, fresh),
                result_type.clone(),
            ),
            Expression::And { left, right } => left
                .refine_parameters(arguments, fresh)
                .and(right.refine_parameters(arguments, fresh)),
            Expression::BitAnd { left, right } => left
                .refine_parameters(arguments, fresh)
                .bit_and(right.refine_parameters(arguments, fresh)),
            Expression::BitOr { left, right } => left
                .refine_parameters(arguments, fresh)
                .bit_or(right.refine_parameters(arguments, fresh)),
            Expression::BitXor { left, right } => left
                .refine_parameters(arguments, fresh)
                .bit_xor(right.refine_parameters(arguments, fresh)),
            Expression::Cast {
                operand,
                target_type,
            } => operand
                .refine_parameters(arguments, fresh)
                .cast(target_type.clone()),
            Expression::CompileTimeConstant(..) => self.clone(),
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => condition
                .refine_parameters(arguments, fresh)
                .conditional_expression(
                    consequent.refine_parameters(arguments, fresh),
                    alternate.refine_parameters(arguments, fresh),
                ),
            Expression::Div { left, right } => left
                .refine_parameters(arguments, fresh)
                .divide(right.refine_parameters(arguments, fresh)),
            Expression::Equals { left, right } => left
                .refine_parameters(arguments, fresh)
                .equals(right.refine_parameters(arguments, fresh)),
            Expression::GreaterOrEqual { left, right } => left
                .refine_parameters(arguments, fresh)
                .greater_or_equal(right.refine_parameters(arguments, fresh)),
            Expression::GreaterThan { left, right } => left
                .refine_parameters(arguments, fresh)
                .greater_than(right.refine_parameters(arguments, fresh)),
            Expression::Join { left, right, path } => left
                .refine_parameters(arguments, fresh)
                .join(right.refine_parameters(arguments, fresh), &path),
            Expression::LessOrEqual { left, right } => left
                .refine_parameters(arguments, fresh)
                .less_or_equal(right.refine_parameters(arguments, fresh)),
            Expression::LessThan { left, right } => left
                .refine_parameters(arguments, fresh)
                .less_than(right.refine_parameters(arguments, fresh)),
            Expression::Mul { left, right } => left
                .refine_parameters(arguments, fresh)
                .multiply(right.refine_parameters(arguments, fresh)),
            Expression::MulOverflows {
                left,
                right,
                result_type,
            } => left.refine_parameters(arguments, fresh).mul_overflows(
                right.refine_parameters(arguments, fresh),
                result_type.clone(),
            ),
            Expression::Ne { left, right } => left
                .refine_parameters(arguments, fresh)
                .not_equals(right.refine_parameters(arguments, fresh)),
            Expression::Neg { operand } => operand.refine_parameters(arguments, fresh).negate(),
            Expression::Not { operand } => {
                operand.refine_parameters(arguments, fresh).logical_not()
            }
            Expression::Offset { left, right } => left
                .refine_parameters(arguments, fresh)
                .offset(right.refine_parameters(arguments, fresh)),
            Expression::Or { left, right } => left
                .refine_parameters(arguments, fresh)
                .or(right.refine_parameters(arguments, fresh)),
            Expression::Reference(path) => {
                // if the path is a parameter, the reference is an artifact of its type
                // and needs to be removed in the call context
                match &path.value {
                    PathEnum::LocalVariable { ordinal }
                        if 0 < *ordinal && *ordinal <= arguments.len() =>
                    {
                        arguments[*ordinal - 1].1.clone()
                    }
                    _ => {
                        let refined_path = path.refine_parameters(arguments, fresh);
                        AbstractValue::make_from(Expression::Reference(refined_path), 1)
                    }
                }
            }
            Expression::Rem { left, right } => left
                .refine_parameters(arguments, fresh)
                .remainder(right.refine_parameters(arguments, fresh)),
            Expression::Shl { left, right } => left
                .refine_parameters(arguments, fresh)
                .shift_left(right.refine_parameters(arguments, fresh)),
            Expression::ShlOverflows {
                left,
                right,
                result_type,
            } => left.refine_parameters(arguments, fresh).shl_overflows(
                right.refine_parameters(arguments, fresh),
                result_type.clone(),
            ),
            Expression::Shr {
                left,
                right,
                result_type,
            } => left.refine_parameters(arguments, fresh).shr(
                right.refine_parameters(arguments, fresh),
                result_type.clone(),
            ),
            Expression::ShrOverflows {
                left,
                right,
                result_type,
            } => left.refine_parameters(arguments, fresh).shr_overflows(
                right.refine_parameters(arguments, fresh),
                result_type.clone(),
            ),
            Expression::Sub { left, right } => left
                .refine_parameters(arguments, fresh)
                .subtract(right.refine_parameters(arguments, fresh)),
            Expression::SubOverflows {
                left,
                right,
                result_type,
            } => left.refine_parameters(arguments, fresh).sub_overflows(
                right.refine_parameters(arguments, fresh),
                result_type.clone(),
            ),
            Expression::UnknownModelField { path, default } => {
                let refined_path = path.refine_parameters(arguments, fresh);
                AbstractValue::make_from(
                    Expression::UnknownModelField {
                        path: refined_path,
                        default: default.clone(),
                    },
                    1,
                )
            }
            Expression::Variable { path, var_type } => {
                let refined_path = path.refine_parameters(arguments, fresh);
                if let PathEnum::Constant { value } = &refined_path.value {
                    value.clone()
                } else {
                    AbstractValue::make_from(
                        Expression::Variable {
                            path: refined_path,
                            var_type: var_type.clone(),
                        },
                        1,
                    )
                }
            }
            Expression::Widen { path, operand } => operand
                .refine_parameters(arguments, fresh)
                .widen(&path.refine_parameters(arguments, fresh)),
        }
    }

    /// Returns a domain that is simplified (refined) by using the current path conditions
    /// (conditions known to be true in the current context). If no refinement is possible
    /// the result is simply a clone of this domain.
    #[logfn_inputs(TRACE)]
    fn refine_with(&self, path_condition: &Self, depth: usize) -> Rc<AbstractValue> {
        if depth >= k_limits::MAX_REFINE_DEPTH {
            return self.clone();
        }
        match &self.expression {
            Expression::Top | Expression::Bottom | Expression::AbstractHeapAddress(..) => {
                self.clone()
            }
            Expression::Add { left, right } => left
                .refine_with(path_condition, depth + 1)
                .addition(right.refine_with(path_condition, depth + 1)),
            Expression::AddOverflows {
                left,
                right,
                result_type,
            } => left.refine_with(path_condition, depth + 1).add_overflows(
                right.refine_with(path_condition, depth + 1),
                result_type.clone(),
            ),
            Expression::And { left, right } => {
                if path_condition.implies(&left) && path_condition.implies(&right) {
                    Rc::new(TRUE)
                } else if path_condition.implies_not(&left) || path_condition.implies_not(&right) {
                    Rc::new(FALSE)
                } else {
                    left.refine_with(path_condition, depth + 1)
                        .and(right.refine_with(path_condition, depth + 1))
                }
            }
            Expression::BitAnd { left, right } => left
                .refine_with(path_condition, depth + 1)
                .bit_and(right.refine_with(path_condition, depth + 1)),
            Expression::BitOr { left, right } => left
                .refine_with(path_condition, depth + 1)
                .bit_or(right.refine_with(path_condition, depth + 1)),
            Expression::BitXor { left, right } => left
                .refine_with(path_condition, depth + 1)
                .bit_xor(right.refine_with(path_condition, depth + 1)),
            Expression::Cast {
                operand,
                target_type,
            } => operand
                .refine_with(path_condition, depth + 1)
                .cast(target_type.clone()),
            Expression::CompileTimeConstant(..) => self.clone(),
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => {
                if path_condition.implies(&condition) {
                    consequent.refine_with(path_condition, depth + 1)
                } else if path_condition.implies_not(&condition) {
                    alternate.refine_with(path_condition, depth + 1)
                } else {
                    let refined_condition = condition.refine_with(path_condition, depth + 1);
                    let refined_consequent = consequent.refine_with(path_condition, depth + 1);
                    let refined_alternate = alternate.refine_with(path_condition, depth + 1);
                    let refined_consequent =
                        refined_consequent.refine_with(&refined_condition, depth + 1);
                    let refined_alternate =
                        refined_alternate.refine_with(&refined_condition, depth + 1);
                    refined_condition.conditional_expression(refined_consequent, refined_alternate)
                }
            }
            Expression::Div { left, right } => left
                .refine_with(path_condition, depth + 1)
                .divide(right.refine_with(path_condition, depth + 1)),
            Expression::Equals { left, right } => left
                .refine_with(path_condition, depth + 1)
                .equals(right.refine_with(path_condition, depth + 1)),
            Expression::GreaterOrEqual { left, right } => left
                .refine_with(path_condition, depth + 1)
                .greater_or_equal(right.refine_with(path_condition, depth + 1)),
            Expression::GreaterThan { left, right } => left
                .refine_with(path_condition, depth + 1)
                .greater_than(right.refine_with(path_condition, depth + 1)),
            Expression::Join { left, right, path } => left
                .refine_with(path_condition, depth + 1)
                .join(right.refine_with(path_condition, depth + 1), &path),
            Expression::LessOrEqual { left, right } => left
                .refine_with(path_condition, depth + 1)
                .less_or_equal(right.refine_with(path_condition, depth + 1)),
            Expression::LessThan { left, right } => left
                .refine_with(path_condition, depth + 1)
                .less_than(right.refine_with(path_condition, depth + 1)),
            Expression::Mul { left, right } => left
                .refine_with(path_condition, depth + 1)
                .multiply(right.refine_with(path_condition, depth + 1)),
            Expression::MulOverflows {
                left,
                right,
                result_type,
            } => left.refine_with(path_condition, depth + 1).mul_overflows(
                right.refine_with(path_condition, depth + 1),
                result_type.clone(),
            ),
            Expression::Ne { left, right } => left
                .refine_with(path_condition, depth + 1)
                .not_equals(right.refine_with(path_condition, depth + 1)),
            Expression::Neg { operand } => operand.refine_with(path_condition, depth + 1).negate(),
            Expression::Not { operand } => {
                if path_condition.implies(&operand) {
                    Rc::new(FALSE)
                } else if path_condition.implies_not(&operand) {
                    Rc::new(TRUE)
                } else {
                    operand.refine_with(path_condition, depth + 1).logical_not()
                }
            }
            Expression::Offset { left, right } => left
                .refine_with(path_condition, depth + 1)
                .offset(right.refine_with(path_condition, depth + 1)),
            Expression::Or { left, right } => {
                if path_condition.implies(&left) || path_condition.implies(&right) {
                    Rc::new(TRUE)
                } else if path_condition.implies_not(&left) && path_condition.implies_not(&right) {
                    Rc::new(FALSE)
                } else {
                    left.refine_with(path_condition, depth + 1)
                        .or(right.refine_with(path_condition, depth + 1))
                }
            }
            Expression::Reference(..) => self.clone(),
            Expression::Rem { left, right } => left
                .refine_with(path_condition, depth + 1)
                .remainder(right.refine_with(path_condition, depth + 1)),
            Expression::Shl { left, right } => left
                .refine_with(path_condition, depth + 1)
                .shift_left(right.refine_with(path_condition, depth + 1)),
            Expression::ShlOverflows {
                left,
                right,
                result_type,
            } => left.refine_with(path_condition, depth + 1).shl_overflows(
                right.refine_with(path_condition, depth + 1),
                result_type.clone(),
            ),
            Expression::Shr {
                left,
                right,
                result_type,
            } => left.refine_with(path_condition, depth + 1).shr(
                right.refine_with(path_condition, depth + 1),
                result_type.clone(),
            ),
            Expression::ShrOverflows {
                left,
                right,
                result_type,
            } => left.refine_with(path_condition, depth + 1).shr_overflows(
                right.refine_with(path_condition, depth + 1),
                result_type.clone(),
            ),
            Expression::Sub { left, right } => left
                .refine_with(path_condition, depth + 1)
                .subtract(right.refine_with(path_condition, depth + 1)),
            Expression::SubOverflows {
                left,
                right,
                result_type,
            } => left.refine_with(path_condition, depth + 1).sub_overflows(
                right.refine_with(path_condition, depth + 1),
                result_type.clone(),
            ),
            Expression::UnknownModelField { .. } => self.clone(),
            Expression::Variable { .. } => {
                if path_condition.implies(&self) {
                    Rc::new(TRUE)
                } else if path_condition.implies_not(&self) {
                    Rc::new(FALSE)
                } else {
                    self.clone()
                }
            }
            Expression::Widen { path, operand } => {
                operand.refine_with(path_condition, depth + 1).widen(&path)
            }
        }
    }

    /// Returns a domain whose corresponding set of concrete values include all of the values
    /// corresponding to self and other. The set of values may be less precise (more inclusive) than
    /// the set returned by join. The chief requirement is that a small number of widen calls
    /// deterministically lead to a set of values that include of the values that could be stored
    /// in memory at the given path.
    #[logfn_inputs(TRACE)]
    fn widen(&self, path: &Rc<Path>) -> Rc<AbstractValue> {
        match self.expression {
            Expression::Widen { .. }
            | Expression::AbstractHeapAddress(..)
            | Expression::CompileTimeConstant(..)
            | Expression::Reference(..)
            | Expression::Variable { .. } => self.clone(),
            _ => AbstractValue::make_from(
                Expression::Widen {
                    path: path.clone(),
                    operand: self.clone(),
                },
                1,
            ),
        }
    }
}
