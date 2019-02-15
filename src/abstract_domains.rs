// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use abstract_value::{AbstractValue, Path};
use constant_domain::ConstantDomain;
use environment::Environment;
use expression::{Expression, ExpressionType};
use rustc::ty::TyKind;
use syntax::ast;

// See https://github.com/facebookexperimental/MIRAI/blob/master/documentation/AbstractValues.md.

/// Basically, this domain is a structured container for other domains. It is also the only
/// client for the other domains.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash)]
pub struct AbstractDomain {
    // todo: make this private
    // This is not a domain element, but a representation of how this instance has been constructed.
    // It is used to refine the instance with respect to path conditions and actual arguments.
    // It is also used to construct corresponding elements from other domains, when needed.
    pub expression: Expression,
    //todo: #30 use cached getters to get specialized domains on demand
}

/// An abstract domain element that all represent the impossible concrete value.
/// I.e. the corresponding set of possible concrete values is empty.
pub const BOTTOM: AbstractDomain = AbstractDomain {
    expression: Expression::Bottom,
};

/// An abstract domain element that all represent the single concrete value, false.
pub const FALSE: AbstractDomain = AbstractDomain {
    expression: Expression::CompileTimeConstant(ConstantDomain::False),
};

/// An abstract domain element that all represents all possible concrete values.
pub const TOP: AbstractDomain = AbstractDomain {
    expression: Expression::Top,
};

/// An abstract domain element that all represent the single concrete value, true.
pub const TRUE: AbstractDomain = AbstractDomain {
    expression: Expression::CompileTimeConstant(ConstantDomain::True),
};

impl<'a> From<&TyKind<'a>> for ExpressionType {
    fn from(ty_kind: &TyKind) -> ExpressionType {
        match ty_kind {
            TyKind::Bool => ExpressionType::Bool,
            TyKind::Char => ExpressionType::Char,
            TyKind::Int(ast::IntTy::Isize) => ExpressionType::Isize,
            TyKind::Int(ast::IntTy::I8) => ExpressionType::I8,
            TyKind::Int(ast::IntTy::I16) => ExpressionType::I16,
            TyKind::Int(ast::IntTy::I32) => ExpressionType::I32,
            TyKind::Int(ast::IntTy::I64) => ExpressionType::I64,
            TyKind::Int(ast::IntTy::I128) => ExpressionType::I128,
            TyKind::Uint(ast::UintTy::Usize) => ExpressionType::Usize,
            TyKind::Uint(ast::UintTy::U8) => ExpressionType::U8,
            TyKind::Uint(ast::UintTy::U16) => ExpressionType::U16,
            TyKind::Uint(ast::UintTy::U32) => ExpressionType::U32,
            TyKind::Uint(ast::UintTy::U64) => ExpressionType::U64,
            TyKind::Uint(ast::UintTy::U128) => ExpressionType::U128,
            TyKind::Float(ast::FloatTy::F32) => ExpressionType::F32,
            TyKind::Float(ast::FloatTy::F64) => ExpressionType::F64,
            _ => ExpressionType::NonPrimitive,
        }
    }
}

impl From<bool> for AbstractDomain {
    fn from(b: bool) -> AbstractDomain {
        if b {
            AbstractDomain {
                expression: Expression::CompileTimeConstant(ConstantDomain::True),
            }
        } else {
            AbstractDomain {
                expression: Expression::CompileTimeConstant(ConstantDomain::False),
            }
        }
    }
}

impl From<ConstantDomain> for AbstractDomain {
    fn from(cv: ConstantDomain) -> AbstractDomain {
        AbstractDomain {
            expression: Expression::CompileTimeConstant(cv),
        }
    }
}

impl From<Expression> for AbstractDomain {
    fn from(expr: Expression) -> AbstractDomain {
        AbstractDomain { expression: expr }
    }
}

impl AbstractDomain {
    /// Returns an element that is "self + other".
    pub fn add(&self, other: &Self) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.add(v2);
            if result != ConstantDomain::Bottom {
                return result.into();
            }
        };
        Expression::Add {
            left: box self.clone(),
            right: box other.clone(),
        }
        .into()
    }

    /// Returns an element that is true if "self + other" is not in range of target_type.
    pub fn add_overflows(&self, other: &Self, target_type: ExpressionType) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.add_overflows(v2, &target_type);
            if result != ConstantDomain::Bottom {
                return result.into();
            }
        };
        Expression::AddOverflows {
            left: box self.clone(),
            right: box other.clone(),
            result_type: target_type,
        }
        .into()
    }

    /// Returns an element that is "self && other".
    pub fn and(&self, other: &Self) -> Self {
        let self_bool = self.as_bool_if_known();
        if let Some(false) = self_bool {
            return false.into();
        };
        let other_bool = other.as_bool_if_known();
        if let Some(false) = other_bool {
            return false.into();
        };
        if self_bool.unwrap_or(false) {
            if other_bool.unwrap_or(false) {
                true.into()
            } else {
                other.clone()
            }
        } else if other_bool.unwrap_or(false)
            || self.is_top()
            || self.is_bottom() && other.is_bottom()
        {
            self.clone()
        } else if other.is_top() {
            other.clone()
        } else {
            // todo: #32 more simplifications
            Expression::And {
                left: box self.clone(),
                right: box other.clone(),
            }
            .into()
        }
    }

    /// The Boolean value of this expression, if known, otherwise None.
    pub fn as_bool_if_known(&self) -> Option<bool> {
        match self.expression {
            Expression::CompileTimeConstant(ConstantDomain::True) => Some(true),
            Expression::CompileTimeConstant(ConstantDomain::False) => Some(false),
            _ => {
                // todo: ask other domains about this (construct some if need be).
                None
            }
        }
    }

    /// Returns an element that is "self & other".
    pub fn bit_and(&self, other: &Self) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.bit_and(v2);
            if result != ConstantDomain::Bottom {
                return result.into();
            }
        };
        Expression::BitAnd {
            left: box self.clone(),
            right: box other.clone(),
        }
        .into()
    }

    /// Returns an element that is "self | other".
    pub fn bit_or(&self, other: &Self) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.bit_or(v2);
            if result != ConstantDomain::Bottom {
                return result.into();
            }
        };
        Expression::BitOr {
            left: box self.clone(),
            right: box other.clone(),
        }
        .into()
    }

    /// Returns an element that is "self ^ other".
    pub fn bit_xor(&self, other: &Self) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.bit_xor(v2);
            if result != ConstantDomain::Bottom {
                return result.into();
            }
        };
        Expression::BitXor {
            left: box self.clone(),
            right: box other.clone(),
        }
        .into()
    }

    /// Returns an element that is "self / other".
    pub fn div(&self, other: &Self) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.div(v2);
            if result != ConstantDomain::Bottom {
                return result.into();
            }
        };
        Expression::Div {
            left: box self.clone(),
            right: box other.clone(),
        }
        .into()
    }

    /// Returns an element that is "self == other".
    pub fn equals(&self, other: &Self) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            return v1.equals(v2).into();
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
                            return true.into();
                        }
                    }
                }
            }
            // x == 0 is the same as !x when x is Boolean variable. Canonicalize it to the latter.
            (
                Expression::Variable { var_type, .. },
                Expression::CompileTimeConstant(ConstantDomain::U128(val)),
            ) => {
                if *var_type == ExpressionType::Bool && *val == 0 {
                    return self.not();
                }
            }
            // !x == 0 is the same as x when x is Boolean variable. Canonicalize it to the latter.
            (
                Expression::Not { operand },
                Expression::CompileTimeConstant(ConstantDomain::U128(val)),
            ) => {
                if let Expression::Variable { var_type, .. } = &operand.expression {
                    if *var_type == ExpressionType::Bool && *val == 0 {
                        return (**operand).clone();
                    }
                }
            }
            _ => {
                // If self and other are the same expression and the expression could not result in NaN
                // and the expression represents exactly one value, we can simplify this to true.
                if self.expression == other.expression {
                    match self.expression {
                        Expression::Top
                        | Expression::Bottom
                        | Expression::Add { .. }
                        | Expression::Div { .. }
                        | Expression::Mul { .. }
                        | Expression::Neg { .. }
                        | Expression::Rem { .. }
                        | Expression::Sub { .. } => {
                            // Could be NaN, because we don't know the type.
                            // todo: infer it from the operands
                        }
                        Expression::CompileTimeConstant(..) | Expression::Variable { .. } => {
                            unreachable!()
                        } // handled above
                        _ => {
                            // Result is a boolean or integer and the expression domain is a singleton set.
                            return true.into();
                        }
                    }
                }
            }
        }
        // Return an equals expression rather than a constant expression.
        Expression::Equals {
            left: box self.clone(),
            right: box other.clone(),
        }
        .into()
    }

    /// Returns an element that is "self >= other".
    pub fn ge(&self, other: &Self) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            return v1.ge(v2).into();
        };
        Expression::GreaterOrEqual {
            left: box self.clone(),
            right: box other.clone(),
        }
        .into()
    }

    /// Returns an element that is "self > other".
    pub fn gt(&self, other: &Self) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            return v1.gt(v2).into();
        };
        Expression::GreaterThan {
            left: box self.clone(),
            right: box other.clone(),
        }
        .into()
    }

    /// Returns true if "self => other" is known at compile time to be true.
    /// Returning false does not imply the implication is false, just that we do not know.
    pub fn implies(&self, other: &Self) -> bool {
        // x => true, is always true
        // false => x, is always true
        // x => x, is always true
        other.as_bool_if_known().unwrap_or(false)
            || !self.as_bool_if_known().unwrap_or(true)
            || self.equals(other).as_bool_if_known().unwrap_or(false)
    }

    /// Returns true if "self => !other" is known at compile time to be true.
    /// Returning false does not imply the implication is false, just that we do not know.
    pub fn implies_not(&self, other: &Self) -> bool {
        // x => !false, is always true
        // false => !x, is always true
        if !other.as_bool_if_known().unwrap_or(true) || !self.as_bool_if_known().unwrap_or(true) {
            return true;
        };
        // !x => !x
        if let Expression::Not { ref operand } = self.expression {
            return (**operand)
                .equals(other)
                .as_bool_if_known()
                .unwrap_or(false);
        }
        false
    }

    /// True if the set of concrete values that correspond to this domain is empty.
    pub fn is_bottom(&self) -> bool {
        match self.expression {
            Expression::Bottom => true,
            _ => false,
        }
    }

    /// True if all possible concrete values are elements of the set corresponding to this domain.
    pub fn is_top(&self) -> bool {
        match self.expression {
            Expression::Top => true,
            _ => false,
        }
    }

    /// Returns a domain whose corresponding set of concrete values include all of the values
    /// corresponding to self and other.
    /// In a context where the join condition is known to be true, the result can be refined to be
    /// just self, correspondingly if it is known to be false, the result can be refined to be just other.
    pub fn join(&self, other: &Self, join_condition: &AbstractDomain) -> Self {
        // If the condition is impossible so is the expression.
        if join_condition.is_bottom() {
            Expression::Bottom.into()
        }
        // c ? x : x is just x, as is true ? x : y
        else if (*self).expression == (*other).expression
            || join_condition.as_bool_if_known().unwrap_or(false)
        {
            self.clone()
        }
        // false ? x : y is just y
        else if !join_condition.as_bool_if_known().unwrap_or(true) {
            other.clone()
        }
        // c ? true : !c is just c
        else if self.as_bool_if_known().unwrap_or(false) && join_condition.not() == *other {
            true.into()
        } else {
            Expression::ConditionalExpression {
                condition: box join_condition.clone(),
                consequent: box self.clone(),
                alternate: box other.clone(),
            }
            .into()
        }
    }

    /// Returns an element that is "self <= other".
    pub fn le(&self, other: &Self) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            return v1.le(v2).into();
        };
        Expression::LessOrEqual {
            left: box self.clone(),
            right: box other.clone(),
        }
        .into()
    }

    /// Returns an element that is self < other
    pub fn lt(&self, other: &Self) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            return v1.lt(v2).into();
        };
        Expression::LessThan {
            left: box self.clone(),
            right: box other.clone(),
        }
        .into()
    }

    /// Returns an element that is "self * other".
    pub fn mul(&self, other: &Self) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.mul(v2);
            if result != ConstantDomain::Bottom {
                return result.into();
            }
        };
        Expression::Mul {
            left: box self.clone(),
            right: box other.clone(),
        }
        .into()
    }

    /// Returns an element that is true if "self * other" is not in range of target_type.
    pub fn mul_overflows(&self, other: &Self, target_type: ExpressionType) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.mul_overflows(v2, &target_type);
            if result != ConstantDomain::Bottom {
                return result.into();
            }
        };
        Expression::MulOverflows {
            left: box self.clone(),
            right: box other.clone(),
            result_type: target_type,
        }
        .into()
    }

    /// Returns an element that is "-self".
    pub fn neg(&self) -> Self {
        if let Expression::CompileTimeConstant(v1) = &self.expression {
            let result = v1.neg();
            if result != ConstantDomain::Bottom {
                return result.into();
            }
        };
        Expression::Neg {
            operand: box self.clone(),
        }
        .into()
    }

    /// Returns an element that is "self != other".
    pub fn not_equals(&self, other: &Self) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            return v1.not_equals(v2).into();
        };
        Expression::Ne {
            left: box self.clone(),
            right: box other.clone(),
        }
        .into()
    }

    /// Returns an element that is "!self".
    pub fn not(&self) -> Self {
        if let Expression::CompileTimeConstant(v1) = &self.expression {
            let result = v1.not();
            if result != ConstantDomain::Bottom {
                return result.into();
            }
        };
        match &self.expression {
            Expression::Bottom => self.clone(),
            Expression::Not { operand } => (**operand).clone(),
            _ => Expression::Not {
                operand: box self.clone(),
            }
            .into(),
        }
    }

    /// Returns an element that is "self.other".
    pub fn offset(&self, other: &Self) -> Self {
        Expression::Offset {
            left: box self.clone(),
            right: box other.clone(),
        }
        .into()
    }

    /// Returns an element that is "self || other".
    pub fn or(&self, other: &Self) -> Self {
        if self.as_bool_if_known().unwrap_or(false) || other.as_bool_if_known().unwrap_or(false) {
            true.into()
        } else if self.is_bottom() || !self.as_bool_if_known().unwrap_or(true) {
            other.clone()
        } else if other.is_bottom() || !other.as_bool_if_known().unwrap_or(true) {
            self.clone()
        } else {
            match (&self.expression, &other.expression) {
                (Expression::Not { ref operand }, _)
                    if operand.equals(other).as_bool_if_known().unwrap_or(false) =>
                {
                    true.into()
                }
                (_, Expression::Not { ref operand })
                    if operand.equals(self).as_bool_if_known().unwrap_or(false) =>
                {
                    true.into()
                }
                _ => Expression::Or {
                    left: box self.clone(),
                    right: box other.clone(),
                }
                .into(),
            }
        }
    }

    /// Returns an element that is "self % other".
    pub fn rem(&self, other: &Self) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.rem(v2);
            if result != ConstantDomain::Bottom {
                return result.into();
            }
        };
        Expression::Rem {
            left: box self.clone(),
            right: box other.clone(),
        }
        .into()
    }

    /// Returns an element that is "self << other".
    pub fn shl(&self, other: &Self) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.shl(v2);
            if result != ConstantDomain::Bottom {
                return result.into();
            }
        };
        Expression::Shl {
            left: box self.clone(),
            right: box other.clone(),
        }
        .into()
    }

    /// Returns an element that is true if "self << other" shifts away all bits.
    pub fn shl_overflows(&self, other: &Self, target_type: ExpressionType) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.shl_overflows(v2, &target_type);
            if result != ConstantDomain::Bottom {
                return result.into();
            }
        };
        Expression::ShlOverflows {
            left: box self.clone(),
            right: box other.clone(),
            result_type: target_type,
        }
        .into()
    }

    /// Returns an element that is "self >> other".
    pub fn shr(&self, other: &Self) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.shr(v2);
            if result != ConstantDomain::Bottom {
                return result.into();
            }
        };
        Expression::Shr {
            left: box self.clone(),
            right: box other.clone(),
        }
        .into()
    }

    /// Returns an element that is true if "self >> other" shifts away all bits.
    pub fn shr_overflows(&self, other: &Self, target_type: ExpressionType) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.shr_overflows(v2, &target_type);
            if result != ConstantDomain::Bottom {
                return result.into();
            }
        };
        Expression::ShrOverflows {
            left: box self.clone(),
            right: box other.clone(),
            result_type: target_type,
        }
        .into()
    }

    /// Returns an element that is "self - other".
    pub fn sub(&self, other: &Self) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.sub(v2);
            if result != ConstantDomain::Bottom {
                return result.into();
            }
        };
        Expression::Sub {
            left: box self.clone(),
            right: box other.clone(),
        }
        .into()
    }

    /// Returns an element that is true if "self - other" is not in range of target_type.
    pub fn sub_overflows(&self, other: &Self, target_type: ExpressionType) -> Self {
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&self.expression, &other.expression)
        {
            let result = v1.sub_overflows(v2, &target_type);
            if result != ConstantDomain::Bottom {
                return result.into();
            }
        };
        Expression::SubOverflows {
            left: box self.clone(),
            right: box other.clone(),
            result_type: target_type,
        }
        .into()
    }

    /// True if all of the concrete values that correspond to self also correspond to other.
    /// Note: !x.subset(y) does not imply y.subset(x).
    pub fn subset(&self, other: &Self) -> bool {
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
            // x is a subset of (condition ? consequent : alternate) x is a subset of both consequent and alternate.
            (
                _,
                Expression::ConditionalExpression {
                    consequent,
                    alternate,
                    ..
                },
            ) => {
                // This is a conservative answer. False does not imply other.subset(self).
                self.subset(&consequent) && self.subset(&alternate)
            }
            // {x} subset {y} iff x = y
            (Expression::AbstractHeapAddress(a1), Expression::AbstractHeapAddress(a2)) => a1 == a2,
            (Expression::CompileTimeConstant(cv1), Expression::CompileTimeConstant(cv2)) => {
                cv1 == cv2
            }
            (Expression::Reference(p1), Expression::Reference(p2)) => p1 == p2,
            // in all other cases we conservatively answer false
            _ => false,
        }
    }

    /// Recursively applies refine_paths to every sub expression of self.
    /// Replaces occurrencs of Expression::Variable(path) with the value at that path
    /// in the given environment (if there is such a value).
    pub fn refine_paths(&self, environment: &mut Environment) -> Self {
        match &self.expression {
            Expression::Top | Expression::Bottom | Expression::AbstractHeapAddress(..) => {
                self.clone()
            }
            Expression::Add { left, right } => left
                .refine_paths(environment)
                .add(&right.refine_paths(environment)),
            Expression::AddOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_paths(environment)
                .add_overflows(&right.refine_paths(environment), result_type.clone()),
            Expression::And { left, right } => left
                .refine_paths(environment)
                .and(&right.refine_paths(environment)),
            Expression::BitAnd { left, right } => left
                .refine_paths(environment)
                .bit_and(&right.refine_paths(environment)),
            Expression::BitOr { left, right } => left
                .refine_paths(environment)
                .bit_or(&right.refine_paths(environment)),
            Expression::BitXor { left, right } => left
                .refine_paths(environment)
                .bit_xor(&right.refine_paths(environment)),
            Expression::CompileTimeConstant(..) => self.clone(),
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => consequent.refine_paths(environment).join(
                &alternate.refine_paths(environment),
                &condition.refine_paths(environment),
            ),
            Expression::Div { left, right } => left
                .refine_paths(environment)
                .div(&right.refine_paths(environment)),
            Expression::Equals { left, right } => left
                .refine_paths(environment)
                .equals(&right.refine_paths(environment)),
            Expression::GreaterOrEqual { left, right } => left
                .refine_paths(environment)
                .ge(&right.refine_paths(environment)),
            Expression::GreaterThan { left, right } => left
                .refine_paths(environment)
                .gt(&right.refine_paths(environment)),
            Expression::LessOrEqual { left, right } => left
                .refine_paths(environment)
                .le(&right.refine_paths(environment)),
            Expression::LessThan { left, right } => left
                .refine_paths(environment)
                .lt(&right.refine_paths(environment)),
            Expression::Mul { left, right } => left
                .refine_paths(environment)
                .mul(&right.refine_paths(environment)),
            Expression::MulOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_paths(environment)
                .mul_overflows(&right.refine_paths(environment), result_type.clone()),
            Expression::Ne { left, right } => left
                .refine_paths(environment)
                .not_equals(&right.refine_paths(environment)),
            Expression::Neg { operand } => operand.refine_paths(environment).neg(),
            Expression::Not { operand } => operand.refine_paths(environment).not(),
            Expression::Offset { left, right } => left
                .refine_paths(environment)
                .offset(&right.refine_paths(environment)),
            Expression::Or { left, right } => left
                .refine_paths(environment)
                .or(&right.refine_paths(environment)),
            Expression::Reference(..) => self.clone(),
            Expression::Rem { left, right } => left
                .refine_paths(environment)
                .rem(&right.refine_paths(environment)),
            Expression::Shl { left, right } => left
                .refine_paths(environment)
                .shl(&right.refine_paths(environment)),
            Expression::ShlOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_paths(environment)
                .shl_overflows(&right.refine_paths(environment), result_type.clone()),
            Expression::Shr { left, right } => left
                .refine_paths(environment)
                .shr(&right.refine_paths(environment)),
            Expression::ShrOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_paths(environment)
                .shr_overflows(&right.refine_paths(environment), result_type.clone()),
            Expression::Sub { left, right } => left
                .refine_paths(environment)
                .sub(&right.refine_paths(environment)),
            Expression::SubOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_paths(environment)
                .sub_overflows(&right.refine_paths(environment), result_type.clone()),
            Expression::Variable { path, .. } => {
                if let Some(val) = environment.value_at(path) {
                    val.domain.clone()
                } else {
                    self.clone()
                }
            }
        }
    }

    /// Recursively applies refine_parameters to every sub expression of self.
    pub fn refine_parameters(&self, arguments: &[AbstractValue]) -> Self {
        match &self.expression {
            Expression::Top | Expression::Bottom | Expression::AbstractHeapAddress(..) => {
                self.clone()
            }
            Expression::Add { left, right } => left
                .refine_parameters(arguments)
                .add(&right.refine_parameters(arguments)),
            Expression::AddOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_parameters(arguments)
                .add_overflows(&right.refine_parameters(arguments), result_type.clone()),
            Expression::And { left, right } => left
                .refine_parameters(arguments)
                .and(&right.refine_parameters(arguments)),
            Expression::BitAnd { left, right } => left
                .refine_parameters(arguments)
                .bit_and(&right.refine_parameters(arguments)),
            Expression::BitOr { left, right } => left
                .refine_parameters(arguments)
                .bit_or(&right.refine_parameters(arguments)),
            Expression::BitXor { left, right } => left
                .refine_parameters(arguments)
                .bit_xor(&right.refine_parameters(arguments)),
            Expression::CompileTimeConstant(..) => self.clone(),
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => consequent.refine_parameters(arguments).join(
                &alternate.refine_parameters(arguments),
                &condition.refine_parameters(arguments),
            ),
            Expression::Div { left, right } => left
                .refine_parameters(arguments)
                .div(&right.refine_parameters(arguments)),
            Expression::Equals { left, right } => left
                .refine_parameters(arguments)
                .equals(&right.refine_parameters(arguments)),
            Expression::GreaterOrEqual { left, right } => left
                .refine_parameters(arguments)
                .ge(&right.refine_parameters(arguments)),
            Expression::GreaterThan { left, right } => left
                .refine_parameters(arguments)
                .gt(&right.refine_parameters(arguments)),
            Expression::LessOrEqual { left, right } => left
                .refine_parameters(arguments)
                .le(&right.refine_parameters(arguments)),
            Expression::LessThan { left, right } => left
                .refine_parameters(arguments)
                .lt(&right.refine_parameters(arguments)),
            Expression::Mul { left, right } => left
                .refine_parameters(arguments)
                .mul(&right.refine_parameters(arguments)),
            Expression::MulOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_parameters(arguments)
                .mul_overflows(&right.refine_parameters(arguments), result_type.clone()),
            Expression::Ne { left, right } => left
                .refine_parameters(arguments)
                .not_equals(&right.refine_parameters(arguments)),
            Expression::Neg { operand } => operand.refine_parameters(arguments).neg(),
            Expression::Not { operand } => operand.refine_parameters(arguments).not(),
            Expression::Offset { left, right } => left
                .refine_parameters(arguments)
                .offset(&right.refine_parameters(arguments)),
            Expression::Or { left, right } => left
                .refine_parameters(arguments)
                .or(&right.refine_parameters(arguments)),
            Expression::Reference(..) => self.clone(),
            Expression::Rem { left, right } => left
                .refine_parameters(arguments)
                .rem(&right.refine_parameters(arguments)),
            Expression::Shl { left, right } => left
                .refine_parameters(arguments)
                .shl(&right.refine_parameters(arguments)),
            Expression::ShlOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_parameters(arguments)
                .shl_overflows(&right.refine_parameters(arguments), result_type.clone()),
            Expression::Shr { left, right } => left
                .refine_parameters(arguments)
                .shr(&right.refine_parameters(arguments)),
            Expression::ShrOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_parameters(arguments)
                .shr_overflows(&right.refine_parameters(arguments), result_type.clone()),
            Expression::Sub { left, right } => left
                .refine_parameters(arguments)
                .sub(&right.refine_parameters(arguments)),
            Expression::SubOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_parameters(arguments)
                .sub_overflows(&right.refine_parameters(arguments), result_type.clone()),
            Expression::Variable { path, .. } => match **path {
                Path::LocalVariable { ordinal } if 0 < ordinal && ordinal <= arguments.len() => {
                    arguments[ordinal - 1].domain.clone()
                }
                _ => self.clone(),
            },
        }
    }

    /// Recursively applies refine_with to every sub expression of self.
    pub fn refine_with(&self, path_condition: &Self) -> Self {
        match &self.expression {
            Expression::Top | Expression::Bottom | Expression::AbstractHeapAddress(..) => {
                self.clone()
            }
            Expression::Add { left, right } => left
                .refine_with(path_condition)
                .add(&right.refine_with(path_condition)),
            Expression::AddOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_with(path_condition)
                .add_overflows(&right.refine_with(path_condition), result_type.clone()),
            Expression::And { left, right } => {
                if path_condition.implies(&**left) && path_condition.implies(&**right) {
                    true.into()
                } else if path_condition.implies_not(&**left)
                    || path_condition.implies_not(&**right)
                {
                    false.into()
                } else {
                    left.refine_with(path_condition)
                        .and(&right.refine_with(path_condition))
                }
            }
            Expression::BitAnd { left, right } => left
                .refine_with(path_condition)
                .bit_and(&right.refine_with(path_condition)),
            Expression::BitOr { left, right } => left
                .refine_with(path_condition)
                .bit_or(&right.refine_with(path_condition)),
            Expression::BitXor { left, right } => left
                .refine_with(path_condition)
                .bit_xor(&right.refine_with(path_condition)),
            Expression::CompileTimeConstant(..) => self.clone(),
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => {
                if path_condition.implies(&**condition) {
                    consequent.refine_with(path_condition)
                } else if path_condition.implies_not(&**condition) {
                    alternate.refine_with(path_condition)
                } else {
                    let refined_condition = condition.refine_with(path_condition);
                    let refined_consequent = consequent.refine_with(path_condition);
                    let refined_alternate = alternate.refine_with(path_condition);
                    let refined_consequent = refined_consequent.refine_with(&refined_condition);
                    let refined_alternate = refined_alternate.refine_with(&refined_condition);
                    Expression::ConditionalExpression {
                        condition: box refined_condition,
                        consequent: box refined_consequent,
                        alternate: box refined_alternate,
                    }
                    .into()
                }
            }
            Expression::Div { left, right } => left
                .refine_with(path_condition)
                .div(&right.refine_with(path_condition)),
            Expression::Equals { left, right } => left
                .refine_with(path_condition)
                .equals(&right.refine_with(path_condition)),
            Expression::GreaterOrEqual { left, right } => left
                .refine_with(path_condition)
                .ge(&right.refine_with(path_condition)),
            Expression::GreaterThan { left, right } => left
                .refine_with(path_condition)
                .gt(&right.refine_with(path_condition)),
            Expression::LessOrEqual { left, right } => left
                .refine_with(path_condition)
                .le(&right.refine_with(path_condition)),
            Expression::LessThan { left, right } => left
                .refine_with(path_condition)
                .lt(&right.refine_with(path_condition)),
            Expression::Mul { left, right } => left
                .refine_with(path_condition)
                .mul(&right.refine_with(path_condition)),
            Expression::MulOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_with(path_condition)
                .mul_overflows(&right.refine_with(path_condition), result_type.clone()),
            Expression::Ne { left, right } => left
                .refine_with(path_condition)
                .not_equals(&right.refine_with(path_condition)),
            Expression::Neg { operand } => operand.refine_with(path_condition).neg(),
            Expression::Not { operand } => {
                if path_condition.implies(&**operand) {
                    false.into()
                } else if path_condition.implies_not(&**operand) {
                    true.into()
                } else {
                    operand.refine_with(path_condition).not()
                }
            }
            Expression::Offset { left, right } => left
                .refine_with(path_condition)
                .offset(&right.refine_with(path_condition)),
            Expression::Or { left, right } => {
                if path_condition.implies(&**left) || path_condition.implies(&**right) {
                    true.into()
                } else if path_condition.implies_not(&**left)
                    && path_condition.implies_not(&**right)
                {
                    false.into()
                } else {
                    left.refine_with(path_condition)
                        .or(&right.refine_with(path_condition))
                }
            }
            Expression::Reference(..) => self.clone(),
            Expression::Rem { left, right } => left
                .refine_with(path_condition)
                .rem(&right.refine_with(path_condition)),
            Expression::Shl { left, right } => left
                .refine_with(path_condition)
                .shl(&right.refine_with(path_condition)),
            Expression::ShlOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_with(path_condition)
                .shl_overflows(&right.refine_with(path_condition), result_type.clone()),
            Expression::Shr { left, right } => left
                .refine_with(path_condition)
                .shr(&right.refine_with(path_condition)),
            Expression::ShrOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_with(path_condition)
                .shr_overflows(&right.refine_with(path_condition), result_type.clone()),
            Expression::Sub { left, right } => left
                .refine_with(path_condition)
                .sub(&right.refine_with(path_condition)),
            Expression::SubOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_with(path_condition)
                .sub_overflows(&right.refine_with(path_condition), result_type.clone()),
            Expression::Variable { .. } => {
                if path_condition.implies(&self) {
                    true.into()
                } else if path_condition.implies_not(&self) {
                    false.into()
                } else {
                    self.clone()
                }
            }
        }
    }

    /// Returns a domain whose corresponding set of concrete values include all of the values
    /// corresponding to self and other.The set of values may be less precise (more inclusive) than
    /// the set returned by join. The chief requirement is that a small number of widen calls
    /// deterministically lead to Top.
    pub fn widen(&self, other: &Self, _join_condition: &AbstractDomain) -> Self {
        if self == other {
            return self.clone();
        };
        //todo: #30 don't get to top quite this quickly.
        Expression::Top.into()
    }
}
