// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::abstract_domains::AbstractDomain;
use crate::abstract_value::Path;
use crate::constant_domain::ConstantDomain;

use std::collections::HashSet;

/// Closely based on the expressions found in MIR.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Expression {
    /// An expression that represents any possible value
    Top,

    /// An expression that represents an impossible value, such as the value returned by function
    /// that always panics.
    Bottom,

    /// An expression that represents a block of memory allocated from the heap.
    /// The value of expression is an ordinal used to distinguish this allocation from
    /// other allocations. Because this is static analysis, a given allocation site will
    /// always result in the same ordinal.
    AbstractHeapAddress(usize),

    /// An expression that is the sum of left and right. +
    Add {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
    },

    /// An expression that is false if left + right overflows.
    AddOverflows {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
        // The type of the result of left + right.
        result_type: ExpressionType,
    },

    /// An expression that is true if both left and right are true. &&
    And {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
    },

    /// An expression that is the bitwise and of left and right. &
    BitAnd {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
    },

    /// An expression that is the bitwise or of left and right. |
    BitOr {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
    },

    /// An expression that is the bitwise xor of left and right. ^
    BitXor {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
    },

    /// An expression that is the operand cast to the target_type. as
    Cast {
        operand: Box<AbstractDomain>,
        target_type: ExpressionType,
    },

    /// An expression that is a compile time constant value, such as a numeric literal or a function.
    CompileTimeConstant(ConstantDomain),

    /// An expression that is either if_true or if_false, depending on the value of condition.
    ConditionalExpression {
        // A condition that results in a Boolean value
        condition: Box<AbstractDomain>,
        // The value of this expression if join_condition is true.
        consequent: Box<AbstractDomain>,
        // The value of this expression if join_condition is false.
        alternate: Box<AbstractDomain>,
    },

    /// An expression that is the left value divided by the right value. /
    Div {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
    },

    /// An expression that is true if left and right are equal. ==
    Equals {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
    },

    /// An expression that is true if left is greater than or equal to right. >=
    GreaterOrEqual {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
    },

    /// An expression that is true if left is greater than right. >
    GreaterThan {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
    },

    /// An expression that is true if left is less than or equal to right. <=
    LessOrEqual {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
    },

    /// An expression that is true if left is less than right. <
    LessThan {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
    },

    /// An expression that is left multiplied by right. *
    Mul {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
    },

    /// An expression that is false if left multiplied by right overflows.
    MulOverflows {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
        // The type of the result of left * right.
        result_type: ExpressionType,
    },

    /// An expression that is true if left and right are not equal. !=
    Ne {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
    },

    /// An expression that is the arithmetic negation of its parameter. -x
    Neg { operand: Box<AbstractDomain> },

    /// An expression that is true if the operand is false.
    Not { operand: Box<AbstractDomain> },

    /// An expression that is true if either one of left or right are true. ||
    Or {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
    },

    /// An expression that is left offset with right. ptr.offset
    Offset {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
    },

    /// The corresponding concrete value is the runtime address of location identified by the path.
    Reference(Path),

    /// An expression that is the remainder of left divided by right. %
    Rem {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
    },

    /// An expression that is the result of left shifted left by right bits. <<
    Shl {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
    },

    /// An expression that is false if left shifted left by right bits would shift way all bits. <<
    ShlOverflows {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
        // The type of the result of left << right.
        result_type: ExpressionType,
    },

    /// An expression that is the result of left shifted right by right bits. >>
    Shr {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
        // The type of the left argument and the result
        result_type: ExpressionType,
    },

    /// An expression that is false if left shifted right by right bits would shift way all bits. >>
    ShrOverflows {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
        // The type of the result of left >> right.
        result_type: ExpressionType,
    },

    /// An expression that is the right subtracted from left. -
    Sub {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
    },

    /// An expression that is false if right subtracted from left overflows. -
    SubOverflows {
        // The value of the left operand.
        left: Box<AbstractDomain>,
        // The value of the right operand.
        right: Box<AbstractDomain>,
        // The type of the result of left - right.
        result_type: ExpressionType,
    },

    /// The unknown value of a place in memory.
    /// This is distinct from Top in that we known something: the place and the type.
    /// This is a useful distinction because it allows us to simplify some expressions
    /// like x == x. The type is needed to prevent this particular optimization if
    /// the variable is a floating point number that could be NaN.
    Variable {
        path: Box<Path>,
        var_type: ExpressionType,
    },
}

impl Expression {
    /// Adds any abstract heap addresses found in the associated expression to the given set.
    pub fn record_heap_addresses(&self, result: &mut HashSet<usize>) {
        match &self {
            Expression::AbstractHeapAddress(ordinal) => {
                result.insert(*ordinal);
            }
            Expression::Add { left, right }
            | Expression::And { left, right }
            | Expression::BitAnd { left, right }
            | Expression::BitOr { left, right }
            | Expression::BitXor { left, right }
            | Expression::Div { left, right }
            | Expression::Equals { left, right }
            | Expression::GreaterOrEqual { left, right }
            | Expression::GreaterThan { left, right }
            | Expression::LessOrEqual { left, right }
            | Expression::LessThan { left, right }
            | Expression::Mul { left, right }
            | Expression::Ne { left, right }
            | Expression::Offset { left, right }
            | Expression::Or { left, right }
            | Expression::Rem { left, right }
            | Expression::Shl { left, right }
            | Expression::Shr { left, right, .. }
            | Expression::Sub { left, right } => {
                left.expression.record_heap_addresses(result);
                right.expression.record_heap_addresses(result);
            }
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => {
                condition.expression.record_heap_addresses(result);
                consequent.expression.record_heap_addresses(result);
                alternate.expression.record_heap_addresses(result);
            }
            Expression::Neg { operand } | Expression::Not { operand } => {
                operand.expression.record_heap_addresses(result);
            }
            Expression::Reference(path) => path.record_heap_addresses(result),
            Expression::Variable { path, .. } => path.record_heap_addresses(result),
            _ => (),
        }
    }
}

/// The type of a place in memory, as understood by MIR.
/// For now, we are only really interested to distinguish between
/// floating point values and other values, because NaN != NaN.
/// In the future the other distinctions may be helpful to SMT solvers.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ExpressionType {
    Bool,
    Char,
    F32,
    F64,
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
    NonPrimitive,
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
}

impl ExpressionType {
    /// Returns true if this type is one of the signed integer types.
    pub fn is_signed_integer(&self) -> bool {
        use self::ExpressionType::*;
        match self {
            I8 | I16 | I32 | I64 | I128 | Isize => true,
            _ => false,
        }
    }

    /// Returns true if this type is one of the unsigned integer types.
    pub fn is_unsigned_integer(&self) -> bool {
        use self::ExpressionType::*;
        match self {
            U8 | U16 | U32 | U64 | U128 | Usize => true,
            _ => false,
        }
    }

    /// Returns the number of bits used to represent the given type, if primitive.
    /// For non primitive types the result is just 0.
    pub fn bit_length(&self) -> u8 {
        use self::ExpressionType::*;
        match self {
            Bool => 1,
            Char => 16,
            F32 => 32,
            F64 => 64,
            I8 => 8,
            I16 => 16,
            I32 => 32,
            I64 => 64,
            I128 => 128,
            Isize => 64,
            NonPrimitive => 0,
            U8 => 8,
            U16 => 16,
            U32 => 32,
            U64 => 64,
            U128 => 128,
            Usize => 64,
        }
    }
}
