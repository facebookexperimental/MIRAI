// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use abstract_domains::AbstractDomain;
use abstract_value::Path;
use constant_value::ConstantValue;

/// Closely based on the expressions found in MIR.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash)]
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

    /// An expression that is a compile time constant value, such as a numeric literal or a function.
    CompileTimeConstant(ConstantValue),

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

/// The type of a place in memory, as understood by MIR.
/// For now, we are only really interested to distinguish between
/// floating point values and other values, because NaN != NaN.
/// In the future the other distinctions may be helpful to SMT solvers.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash)]
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
