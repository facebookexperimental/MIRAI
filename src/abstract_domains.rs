// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
#![allow(clippy::float_cmp)]

use abstract_value::{AbstractValue, Path};
use constant_value::ConstantValue;
use rustc::ty::TyKind;
use syntax::ast;

// See https://github.com/facebookexperimental/MIRAI/blob/master/documentation/AbstractValues.md.

/// A collection of abstract domains associated with a particular abstract value.
/// The expression domain captures the precise expression that resulted in the abstract
/// value. It can be used to derive any other kind of abstract domain on demand.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash)]
pub struct AbstractDomains {
    pub expression_domain: ExpressionDomain,
    //todo: #30 use cached getters to get other domains on demand
}

/// A collection of abstract domains that all represent the impossible abstract value.
/// I.e. the corresponding set of possible concrete values is empty.
pub const BOTTOM: AbstractDomains = AbstractDomains {
    expression_domain: ExpressionDomain::Bottom,
};

/// A collection of abstract domains that all represent the single concrete value, false.
pub const FALSE: AbstractDomains = AbstractDomains {
    expression_domain: ExpressionDomain::CompileTimeConstant(ConstantValue::False),
};

/// A collection of abstract domains that all represent the universal abstract value.
/// I.e. the corresponding set of possible concrete values includes every possible concrete value.
pub const TOP: AbstractDomains = AbstractDomains {
    expression_domain: ExpressionDomain::Top,
};

/// A collection of abstract domains that all represent the single concrete value, true.
pub const TRUE: AbstractDomains = AbstractDomains {
    expression_domain: ExpressionDomain::CompileTimeConstant(ConstantValue::True),
};

impl AbstractDomains {
    /// The Boolean value of this expression, if known, otherwise None.
    pub fn as_bool_if_known(&self) -> Option<bool> {
        self.expression_domain.as_bool_if_known()
    }

    /// Applies "add_overflows" to every pair of domain elements and returns the collection of results.
    pub fn add_overflows(
        &self,
        other: &AbstractDomains,
        target_type: ExpressionType,
    ) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self
                .expression_domain
                .add_overflows(&other.expression_domain, target_type),
        }
    }

    /// Applies "add" to every pair of domain elements and returns the collection of results.
    pub fn add(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.add(&other.expression_domain),
        }
    }

    /// Applies "and" to every pair of domain elements and returns the collection of results.
    pub fn and(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.and(&other.expression_domain),
        }
    }

    /// Applies "bit_and" to every pair of domain elements and returns the collection of results.
    pub fn bit_and(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.bit_and(&other.expression_domain),
        }
    }

    /// Applies "bit_or" to every pair of domain elements and returns the collection of results.
    pub fn bit_or(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.bit_or(&other.expression_domain),
        }
    }

    /// Applies "bit_xor" to every pair of domain elements and returns the collection of results.
    pub fn bit_xor(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.bit_xor(&other.expression_domain),
        }
    }

    /// Applies "div" to every pair of domain elements and returns the collection of results.
    pub fn div(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.div(&other.expression_domain),
        }
    }

    /// Applies "equals" to every pair of domain elements and returns the collection of results.
    pub fn equals(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.equals(&other.expression_domain),
        }
    }

    /// Applies "ge" to every pair of domain elements and returns the collection of results.
    pub fn ge(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.ge(&other.expression_domain),
        }
    }

    /// Applies "gt" to every pair of domain elements and returns the collection of results.
    pub fn gt(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.gt(&other.expression_domain),
        }
    }

    /// True if all of the abstract domains in this collection correspond to an empty set of concrete values.
    pub fn is_bottom(&self) -> bool {
        self.expression_domain.is_bottom()
    }

    /// True if all of the abstract domains in this collection correspond to the set of all possible concrete values.
    pub fn is_top(&self) -> bool {
        self.expression_domain.is_top()
    }

    /// Joins all of the abstract domains in the two collections to form a single collection.
    /// In a context where the join condition is known to be true, the result can be refined to be
    /// just self, correspondingly if it is known to be false, the result can be refined to be just other.
    pub fn join(
        &self,
        other: &AbstractDomains,
        join_condition: &AbstractDomains,
    ) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self
                .expression_domain
                .join(&other.expression_domain, &join_condition),
        }
    }

    /// Applies "le" to every pair of domain elements and returns the collection of results.
    pub fn le(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.le(&other.expression_domain),
        }
    }

    /// Applies "lt" to every pair of domain elements and returns the collection of results.
    pub fn lt(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.lt(&other.expression_domain),
        }
    }

    /// Applies "mul" to every pair of domain elements and returns the collection of results.
    pub fn mul(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.mul(&other.expression_domain),
        }
    }

    /// Applies "mul_overflows" to every pair of domain elements and returns the collection of results.
    pub fn mul_overflows(
        &self,
        other: &AbstractDomains,
        target_type: ExpressionType,
    ) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self
                .expression_domain
                .mul_overflows(&other.expression_domain, target_type),
        }
    }

    /// Applies "neg" to every domain element and returns the collection of results.
    pub fn neg(&self) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.neg(),
        }
    }

    /// Applies "not_equals" to every pair of domain elements and returns the collection of results.
    pub fn not_equals(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.not_equals(&other.expression_domain),
        }
    }

    /// Applies "not" to every domain element and returns the collection of results.
    pub fn not(&self) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.not(),
        }
    }

    /// Applies "offset" to every pair of domain elements and returns the collection of results.
    pub fn offset(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.offset(&other.expression_domain),
        }
    }

    /// Applies "or" to every pair of domain elements and returns the collection of results.
    pub fn or(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.or(&other.expression_domain),
        }
    }

    /// Applies refine_parameters to every domain element and returns the collection of results.
    pub fn refine_parameters(&self, arguments: &[AbstractValue]) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.refine_parameters(arguments),
        }
    }

    /// Applies "rem" to every pair of domain elements and returns the collection of results.
    pub fn rem(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.rem(&other.expression_domain),
        }
    }

    /// Applies "shl" to every pair of domain elements and returns the collection of results.
    pub fn shl(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.shl(&other.expression_domain),
        }
    }

    /// Applies "shl_overflows" to every pair of domain elements and returns the collection of results.
    pub fn shl_overflows(
        &self,
        other: &AbstractDomains,
        target_type: ExpressionType,
    ) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self
                .expression_domain
                .shl_overflows(&other.expression_domain, target_type),
        }
    }

    /// Applies "shr" to every pair of domain elements and returns the collection of results.
    pub fn shr(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.shr(&other.expression_domain),
        }
    }

    /// Applies "shr_overflows" to every pair of domain elements and returns the collection of results.
    pub fn shr_overflows(
        &self,
        other: &AbstractDomains,
        target_type: ExpressionType,
    ) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self
                .expression_domain
                .shr_overflows(&other.expression_domain, target_type),
        }
    }

    /// Applies "sub" to every pair of domain elements and returns the collection of results.
    pub fn sub(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.sub(&other.expression_domain),
        }
    }

    /// Applies "sub_overflows" to every pair of domain elements and returns the collection of results.
    pub fn sub_overflows(
        &self,
        other: &AbstractDomains,
        target_type: ExpressionType,
    ) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self
                .expression_domain
                .sub_overflows(&other.expression_domain, target_type),
        }
    }

    /// Widen all of the abstract domains in the two collections to form a single collection.
    /// The join condition is supplied to inform the widen operation, but the result is not
    /// required to be in a form that can be refined using the join condition.
    pub fn widen(
        &self,
        other: &AbstractDomains,
        join_condition: &AbstractDomains,
    ) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self
                .expression_domain
                .widen(&other.expression_domain, &join_condition),
        }
    }

    /// True if for each abstract domains in the self collection, all of its concrete values are
    /// elements of the corresponding set of the same domain in other.
    pub fn subset(&self, other: &AbstractDomains) -> bool {
        self.expression_domain.subset(&other.expression_domain)
    }
}

/// An abstract domain defines a set of concrete values in some way.
pub trait AbstractDomain {
    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "+" operation over the elements of the cross product of self and other.
    fn add(&self, other: &Self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete add_overflows operation over the elements of the cross product of self and other.
    fn add_overflows(&self, other: &Self, target_type: ExpressionType) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "&&" operation over the elements of the cross product of self and other.
    fn and(&self, other: &Self) -> Self;

    /// The Boolean value of this expression, if known, otherwise None.
    fn as_bool_if_known(&self) -> Option<bool>;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "&" operation over the elements of the cross product of self and other.
    fn bit_and(&self, other: &Self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "|" operation over the elements of the cross product of self and other.
    fn bit_or(&self, other: &Self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "^" operation over the elements of the cross product of self and other.
    fn bit_xor(&self, other: &Self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "/" operation over the elements of the cross product of self and other.
    fn div(&self, other: &Self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "==" operation over the elements of the cross product of self and other.
    fn equals(&self, other: &Self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete ">=" operation over the elements of the cross product of self and other.
    fn ge(&self, other: &Self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete ">" operation over the elements of the cross product of self and other.
    fn gt(&self, other: &Self) -> Self;

    /// True if the set of concrete values that correspond to this domain is empty.
    fn is_bottom(&self) -> bool;

    /// True if all possible concrete values are elements of the set corresponding to this domain.
    fn is_top(&self) -> bool;

    /// Returns a domain whose corresponding set of concrete values include all of the values
    /// corresponding to self and other.
    /// In a context where the join condition is known to be true, the result can be refined to be
    /// just self, correspondingly if it is known to be false, the result can be refined to be just other.
    fn join(&self, other: &Self, join_condition: &AbstractDomains) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "<=" operation over the elements of the cross product of self and other.
    fn le(&self, other: &Self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "<" operation over the elements of the cross product of self and other.
    fn lt(&self, other: &Self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "*" operation over the elements of the cross product of self and other.
    fn mul(&self, other: &Self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete mul_overflows operation over the elements of the cross product of self and other.
    fn mul_overflows(&self, other: &Self, target_type: ExpressionType) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "-" operation over the elements of self.
    fn neg(&self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "!=" operation over the elements of the cross product of self and other.
    fn not_equals(&self, other: &Self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "!" operation over the elements of self.
    fn not(&self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "ptr.offset" operation over the elements of the cross product of self and other.
    fn offset(&self, other: &Self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "||" operation over the elements of the cross product of self and other.
    fn or(&self, other: &Self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "%" operation over the elements of the cross product of self and other.
    fn rem(&self, other: &Self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "<<" operation over the elements of the cross product of self and other.
    fn shl(&self, other: &Self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete shl_overflows operation over the elements of the cross product of self and other.
    fn shl_overflows(&self, other: &Self, target_type: ExpressionType) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete ">>" operation over the elements of the cross product of self and other.
    fn shr(&self, other: &Self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete shr_overflows operation over the elements of the cross product of self and other.
    fn shr_overflows(&self, other: &Self, target_type: ExpressionType) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "-" operation over the elements of the cross product of self and other.
    fn sub(&self, other: &Self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete sub_overflows operation over the elements of the cross product of self and other.
    fn sub_overflows(&self, other: &Self, target_type: ExpressionType) -> Self;

    /// True if all of the concrete values that correspond to self also correspond to other.
    fn subset(&self, other: &Self) -> bool;

    /// Applies refine_parameters to every domain element and returns the collection of results.
    fn refine_parameters(&self, arguments: &[AbstractValue]) -> Self;

    /// Returns a domain whose corresponding set of concrete values include all of the values
    /// corresponding to self and other.The set of values may be less precise (more inclusive) than
    /// the set returned by join. The chief requirement is that a small number of widen calls
    /// deterministically lead to Top.
    fn widen(&self, other: &Self, join_condition: &AbstractDomains) -> Self;
}

/// An abstract domain that uses a functional (side effect free) expression that precisely tracks
/// a single value.
/// Note: that value might not be known at compile time, so some operations on the domain
/// may conservatively expand the set of of values that correspond to the domain to more than
/// just one element. See for example the subset operation.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash)]
pub enum ExpressionDomain {
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
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// An expression that is false if left + right overflows.
    AddOverflows {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
        // The type of the result of left + right.
        result_type: ExpressionType,
    },

    /// An expression that is true if both left and right are true. &&
    And {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// An expression that is the bitwise and of left and right. &
    BitAnd {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// An expression that is the bitwise or of left and right. |
    BitOr {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// An expression that is the bitwise xor of left and right. ^
    BitXor {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// An expression that is a compile time constant value, such as a numeric literal or a function.
    CompileTimeConstant(ConstantValue),

    /// An expression that is either if_true or if_false, depending on the value of condition.
    ConditionalExpression {
        // A condition that results in a Boolean value
        condition: Box<AbstractDomains>,
        // The value of this expression if join_condition is true.
        consequent: Box<ExpressionDomain>,
        // The value of this expression if join_condition is false.
        alternate: Box<ExpressionDomain>,
    },

    /// An expression that is the left value divided by the right value. /
    Div {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// An expression that is true if left and right are equal. ==
    Equals {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// An expression that is true if left is greater than or equal to right. >=
    GreaterOrEqual {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// An expression that is true if left is greater than right. >
    GreaterThan {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// An expression that is true if left is less than or equal to right. <=
    LessOrEqual {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// An expression that is true if left is less than right. <
    LessThan {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// An expression that is left multiplied by right. *
    Mul {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// An expression that is false if left multiplied by right overflows.
    MulOverflows {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
        // The type of the result of left * right.
        result_type: ExpressionType,
    },

    /// An expression that is true if left and right are not equal. !=
    Ne {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// An expression that is the arithmetic negation of its parameter. -x
    Neg { operand: Box<ExpressionDomain> },

    /// An expression that is true if the operand is false.
    Not { operand: Box<ExpressionDomain> },

    /// An expression that is true if either one of left or right are true. ||
    Or {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// An expression that is left offset with right. ptr.offset
    Offset {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// The corresponding concrete value is the runtime address of location identified by the path.
    Reference(Path),

    /// An expression that is the remainder of left divided by right. %
    Rem {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// An expression that is the result of left shifted left by right bits. <<
    Shl {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// An expression that is false if left shifted left by right bits would shift way all bits. <<
    ShlOverflows {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
        // The type of the result of left << right.
        result_type: ExpressionType,
    },

    /// An expression that is the result of left shifted right by right bits. >>
    Shr {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// An expression that is false if left shifted right by right bits would shift way all bits. >>
    ShrOverflows {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
        // The type of the result of left >> right.
        result_type: ExpressionType,
    },

    /// An expression that is the right subtracted from left. -
    Sub {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// An expression that is false if right subtracted from left overflows. -
    SubOverflows {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
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

impl From<bool> for ExpressionDomain {
    fn from(b: bool) -> ExpressionDomain {
        if b {
            ExpressionDomain::CompileTimeConstant(ConstantValue::True)
        } else {
            ExpressionDomain::CompileTimeConstant(ConstantValue::False)
        }
    }
}

impl AbstractDomain for ExpressionDomain {
    /// Returns an expression that is "self + other".
    fn add(&self, other: &Self) -> Self {
        match (self, other) {
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(val2)),
            ) => {
                let result = f32::from_bits(*val1) + f32::from_bits(*val2);
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(result.to_bits()))
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(val2)),
            ) => {
                let result = f64::from_bits(*val1) + f64::from_bits(*val2);
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(result.to_bits()))
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val2)),
            ) => {
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1.wrapping_add(*val2)))
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val2)),
            ) => {
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1.wrapping_add(*val2)))
            }
            _ => ExpressionDomain::Add {
                left: box self.clone(),
                right: box other.clone(),
            },
        }
    }

    /// Returns an expression that is true if "self + other" is not in range of target_type.
    fn add_overflows(&self, other: &Self, target_type: ExpressionType) -> Self {
        match (self, other) {
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val2)),
            ) => {
                let result = match target_type {
                    ExpressionType::Isize => {
                        isize::overflowing_add(*val1 as isize, *val2 as isize).1
                    }
                    ExpressionType::I128 => i128::overflowing_add(*val1, *val2).1,
                    ExpressionType::I64 => i64::overflowing_add(*val1 as i64, *val2 as i64).1,
                    ExpressionType::I32 => i32::overflowing_add(*val1 as i32, *val2 as i32).1,
                    ExpressionType::I16 => i16::overflowing_add(*val1 as i16, *val2 as i16).1,
                    ExpressionType::I8 => i8::overflowing_add(*val1 as i8, *val2 as i8).1,
                    _ => {
                        println!("{:?}", target_type);
                        unreachable!()
                    }
                };
                result.into()
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val2)),
            ) => {
                let result = match target_type {
                    ExpressionType::Usize => {
                        usize::overflowing_add(*val1 as usize, *val2 as usize).1
                    }
                    ExpressionType::U128 => u128::overflowing_add(*val1, *val2).1,
                    ExpressionType::U64 => u64::overflowing_add(*val1 as u64, *val2 as u64).1,
                    ExpressionType::U32 => u32::overflowing_add(*val1 as u32, *val2 as u32).1,
                    ExpressionType::U16 => u16::overflowing_add(*val1 as u16, *val2 as u16).1,
                    ExpressionType::U8 => u8::overflowing_add(*val1 as u8, *val2 as u8).1,
                    _ => {
                        println!("{:?}", target_type);
                        unreachable!()
                    }
                };
                result.into()
            }
            _ => ExpressionDomain::AddOverflows {
                left: box self.clone(),
                right: box other.clone(),
                result_type: target_type,
            },
        }
    }

    /// Returns an expression that is "self && other".
    fn and(&self, other: &Self) -> Self {
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
                ExpressionDomain::CompileTimeConstant(ConstantValue::True)
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
            ExpressionDomain::And {
                left: box self.clone(),
                right: box other.clone(),
            }
        }
    }

    /// The Boolean value of this expression, if known, otherwise None.
    fn as_bool_if_known(&self) -> Option<bool> {
        match self {
            ExpressionDomain::CompileTimeConstant(ConstantValue::True) => Some(true),
            ExpressionDomain::CompileTimeConstant(ConstantValue::False) => Some(false),
            _ => None,
        }
    }

    /// Returns an expression that is "self & other".
    fn bit_and(&self, other: &Self) -> Self {
        match (self, other) {
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val2)),
            ) => ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1 & val2)),
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val2)),
            ) => ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1 & val2)),
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::True),
                ExpressionDomain::CompileTimeConstant(ConstantValue::True),
            ) => true.into(),
            (ExpressionDomain::CompileTimeConstant(ConstantValue::False), _)
            | (_, ExpressionDomain::CompileTimeConstant(ConstantValue::False)) => false.into(),
            _ => ExpressionDomain::BitAnd {
                left: box self.clone(),
                right: box other.clone(),
            },
        }
    }

    /// Returns an expression that is "self | other".
    fn bit_or(&self, other: &Self) -> Self {
        match (self, other) {
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val2)),
            ) => ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1 | val2)),
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val2)),
            ) => ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1 | val2)),
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::False),
                ExpressionDomain::CompileTimeConstant(ConstantValue::False),
            ) => false.into(),
            (ExpressionDomain::CompileTimeConstant(ConstantValue::True), _)
            | (_, ExpressionDomain::CompileTimeConstant(ConstantValue::True)) => true.into(),
            _ => ExpressionDomain::BitOr {
                left: box self.clone(),
                right: box other.clone(),
            },
        }
    }

    /// Returns an expression that is "self ^ other".
    fn bit_xor(&self, other: &Self) -> Self {
        match (self, other) {
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val2)),
            ) => ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1 ^ val2)),
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val2)),
            ) => ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1 ^ val2)),
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::False),
                ExpressionDomain::CompileTimeConstant(ConstantValue::False),
            )
            | (
                ExpressionDomain::CompileTimeConstant(ConstantValue::True),
                ExpressionDomain::CompileTimeConstant(ConstantValue::True),
            ) => false.into(),
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::True),
                ExpressionDomain::CompileTimeConstant(ConstantValue::False),
            )
            | (
                ExpressionDomain::CompileTimeConstant(ConstantValue::False),
                ExpressionDomain::CompileTimeConstant(ConstantValue::True),
            ) => true.into(),
            _ => ExpressionDomain::BitXor {
                left: box self.clone(),
                right: box other.clone(),
            },
        }
    }

    /// Returns an expression that is "self / other".
    fn div(&self, other: &Self) -> Self {
        match (self, other) {
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(val2)),
            ) => {
                let result = f32::from_bits(*val1) / f32::from_bits(*val2);
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(result.to_bits()))
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(val2)),
            ) => {
                let result = f64::from_bits(*val1) / f64::from_bits(*val2);
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(result.to_bits()))
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val2)),
            ) => {
                if *val2 == 0 {
                    ExpressionDomain::Bottom
                } else {
                    ExpressionDomain::CompileTimeConstant(ConstantValue::I128(*val1 / *val2))
                }
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val2)),
            ) => {
                if *val2 == 0 {
                    ExpressionDomain::Bottom
                } else {
                    ExpressionDomain::CompileTimeConstant(ConstantValue::U128(*val1 / *val2))
                }
            }
            _ => ExpressionDomain::Div {
                left: box self.clone(),
                right: box other.clone(),
            },
        }
    }

    /// Returns an expression that is "self == other".
    fn equals(&self, other: &Self) -> Self {
        match (self, other) {
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(val2)),
            ) => {
                let result = f32::from_bits(*val1) == f32::from_bits(*val2);
                return result.into();
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(val2)),
            ) => {
                let result = f64::from_bits(*val1) == f64::from_bits(*val2);
                return result.into();
            }
            (
                ExpressionDomain::CompileTimeConstant(cv1),
                ExpressionDomain::CompileTimeConstant(cv2),
            ) => {
                return (cv1 == cv2).into();
            }
            // If self and other are the same location in memory, return true unless the value might be NaN.
            (
                ExpressionDomain::Variable {
                    path: p1,
                    var_type: t1,
                },
                ExpressionDomain::Variable {
                    path: p2,
                    var_type: t2,
                },
            ) => {
                if **p1 == **p2 {
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
                ExpressionDomain::Variable { var_type, .. },
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val)),
            ) => {
                if *var_type == ExpressionType::Bool && *val == 0 {
                    return self.not();
                }
            }
            // !x == 0 is the same as x when x is Boolean variable. Canonicalize it to the latter.
            (
                ExpressionDomain::Not { operand },
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val)),
            ) => {
                if let ExpressionDomain::Variable { ref var_type, .. } = **operand {
                    if *var_type == ExpressionType::Bool && *val == 0 {
                        return (**operand).clone();
                    }
                }
            }
            _ => {
                // If self and other are the same expression and the expression could not result in NaN
                // and the expression represents exactly one value, we can simplify this to true.
                if self == other {
                    match self {
                        ExpressionDomain::Top
                        | ExpressionDomain::Bottom
                        | ExpressionDomain::Add { .. }
                        | ExpressionDomain::Div { .. }
                        | ExpressionDomain::Mul { .. }
                        | ExpressionDomain::Neg { .. }
                        | ExpressionDomain::Rem { .. }
                        | ExpressionDomain::Sub { .. } => {
                            // Could be NaN, because we don't know the type.
                            // todo: infer it from the operands
                        }
                        ExpressionDomain::CompileTimeConstant(..)
                        | ExpressionDomain::Variable { .. } => unreachable!(), // handled above
                        _ => {
                            // Result is a boolean or integer and the expression domain is a singleton set.
                            return true.into();
                        }
                    }
                }
            }
        }
        // Return an equals expression rather than a constant expression.
        ExpressionDomain::Equals {
            left: box self.clone(),
            right: box other.clone(),
        }
    }

    /// Returns an expression that is "self >= other".
    fn ge(&self, other: &Self) -> Self {
        match (self, other) {
            (
                ExpressionDomain::CompileTimeConstant(cv1),
                ExpressionDomain::CompileTimeConstant(cv2),
            ) => (cv1 >= cv2).into(),
            _ => ExpressionDomain::GreaterOrEqual {
                left: box self.clone(),
                right: box other.clone(),
            },
        }
    }

    /// Returns an expression that is "self > other".
    fn gt(&self, other: &Self) -> Self {
        match (self, other) {
            (
                ExpressionDomain::CompileTimeConstant(cv1),
                ExpressionDomain::CompileTimeConstant(cv2),
            ) => (cv1 > cv2).into(),
            _ => ExpressionDomain::GreaterThan {
                left: box self.clone(),
                right: box other.clone(),
            },
        }
    }

    /// True if the set of concrete values that correspond to this domain is empty.
    fn is_bottom(&self) -> bool {
        match self {
            ExpressionDomain::Bottom => true,
            _ => false,
        }
    }

    /// True if all possible concrete values are elements of the set corresponding to this domain.
    fn is_top(&self) -> bool {
        match self {
            ExpressionDomain::Top => true,
            _ => false,
        }
    }

    /// Returns a domain whose corresponding set of concrete values include all of the values
    /// corresponding to self and other.
    /// In a context where the join condition is known to be true, the result can be refined to be
    /// just self, correspondingly if it is known to be false, the result can be refined to be just other.
    fn join(&self, other: &Self, join_condition: &AbstractDomains) -> Self {
        // If the condition is impossible so is the expression.
        if join_condition.is_bottom() {
            ExpressionDomain::Bottom
        }
        // c ? x : x is just x, as is true ? x : y
        else if (*self) == *other || join_condition.as_bool_if_known().unwrap_or(false) {
            self.clone()
        }
        // false ? x : y is just y
        else if !join_condition.as_bool_if_known().unwrap_or(true) {
            other.clone()
        }
        // c ? true : !c is just c
        else if self.as_bool_if_known().unwrap_or(false)
            && join_condition.expression_domain.not() == *other
        {
            true.into()
        } else {
            ExpressionDomain::ConditionalExpression {
                condition: box join_condition.clone(),
                consequent: box self.clone(),
                alternate: box other.clone(),
            }
        }
    }

    /// Returns an expression that is "self <= other".
    fn le(&self, other: &Self) -> Self {
        match (self, other) {
            (
                ExpressionDomain::CompileTimeConstant(cv1),
                ExpressionDomain::CompileTimeConstant(cv2),
            ) => (cv1 <= cv2).into(),
            _ => ExpressionDomain::LessOrEqual {
                left: box self.clone(),
                right: box other.clone(),
            },
        }
    }

    /// Returns an expression that is self < other
    fn lt(&self, other: &Self) -> Self {
        match (self, other) {
            (
                ExpressionDomain::CompileTimeConstant(cv1),
                ExpressionDomain::CompileTimeConstant(cv2),
            ) => (cv1 < cv2).into(),
            _ => ExpressionDomain::LessThan {
                left: box self.clone(),
                right: box other.clone(),
            },
        }
    }

    /// Returns an expression that is "self * other".
    fn mul(&self, other: &Self) -> Self {
        match (self, other) {
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(val2)),
            ) => {
                let result = f32::from_bits(*val1) * f32::from_bits(*val2);
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(result.to_bits()))
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(val2)),
            ) => {
                let result = f64::from_bits(*val1) * f64::from_bits(*val2);
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(result.to_bits()))
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val2)),
            ) => {
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1.wrapping_mul(*val2)))
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val2)),
            ) => {
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1.wrapping_mul(*val2)))
            }
            _ => ExpressionDomain::Mul {
                left: box self.clone(),
                right: box other.clone(),
            },
        }
    }

    /// Returns an expression that is true if "self * other" is not in range of target_type.
    fn mul_overflows(&self, other: &Self, target_type: ExpressionType) -> Self {
        match (self, other) {
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val2)),
            ) => {
                let result = match target_type {
                    ExpressionType::I128 => i128::overflowing_mul(*val1, *val2).1,
                    ExpressionType::I64 => i64::overflowing_mul(*val1 as i64, *val2 as i64).1,
                    ExpressionType::I32 => i32::overflowing_mul(*val1 as i32, *val2 as i32).1,
                    ExpressionType::I16 => i16::overflowing_mul(*val1 as i16, *val2 as i16).1,
                    ExpressionType::I8 => i8::overflowing_mul(*val1 as i8, *val2 as i8).1,
                    _ => unreachable!(),
                };
                result.into()
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val2)),
            ) => {
                let result = match target_type {
                    ExpressionType::U128 => u128::overflowing_mul(*val1, *val2).1,
                    ExpressionType::U64 => u64::overflowing_mul(*val1 as u64, *val2 as u64).1,
                    ExpressionType::U32 => u32::overflowing_mul(*val1 as u32, *val2 as u32).1,
                    ExpressionType::U16 => u16::overflowing_mul(*val1 as u16, *val2 as u16).1,
                    ExpressionType::U8 => u8::overflowing_mul(*val1 as u8, *val2 as u8).1,
                    _ => unreachable!(),
                };
                result.into()
            }
            _ => ExpressionDomain::MulOverflows {
                left: box self.clone(),
                right: box other.clone(),
                result_type: target_type,
            },
        }
    }

    /// Returns an expression that is "-self".
    fn neg(&self) -> Self {
        match self {
            ExpressionDomain::CompileTimeConstant(ConstantValue::F32(val)) => {
                let result = -f32::from_bits(*val);
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(result.to_bits()))
            }
            ExpressionDomain::CompileTimeConstant(ConstantValue::F64(val)) => {
                let result = -f64::from_bits(*val);
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(result.to_bits()))
            }
            ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val)) => {
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val.wrapping_neg()))
            }
            ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val)) => {
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val.wrapping_neg()))
            }
            _ => ExpressionDomain::Neg {
                operand: box self.clone(),
            },
        }
    }

    /// Returns an expression that is "self != other".
    fn not_equals(&self, other: &Self) -> Self {
        match (self, other) {
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(val2)),
            ) => {
                let result = f32::from_bits(*val1) != f32::from_bits(*val2);
                result.into()
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(val2)),
            ) => {
                let result = f64::from_bits(*val1) != f64::from_bits(*val2);
                result.into()
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val2)),
            ) => (val1 != val2).into(),
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val2)),
            ) => (val1 != val2).into(),
            _ => ExpressionDomain::Ne {
                left: box self.clone(),
                right: box other.clone(),
            },
        }
    }

    /// Returns an expression that is "!self".
    fn not(&self) -> Self {
        match self {
            ExpressionDomain::CompileTimeConstant(ConstantValue::False) => true.into(),
            ExpressionDomain::CompileTimeConstant(ConstantValue::True) => false.into(),
            ExpressionDomain::Bottom => self.clone(),
            ExpressionDomain::Not { operand } => (**operand).clone(),
            _ => ExpressionDomain::Not {
                operand: box self.clone(),
            },
        }
    }

    /// Returns an expression that is "self.other".
    fn offset(&self, other: &Self) -> Self {
        ExpressionDomain::Offset {
            left: box self.clone(),
            right: box other.clone(),
        }
    }

    /// Returns an expression that is "self || other".
    fn or(&self, other: &Self) -> Self {
        if self.as_bool_if_known().unwrap_or(false) || other.as_bool_if_known().unwrap_or(false) {
            true.into()
        } else if self.is_bottom() || !self.as_bool_if_known().unwrap_or(true) {
            other.clone()
        } else if other.is_bottom() || !other.as_bool_if_known().unwrap_or(true) {
            self.clone()
        } else {
            match (self, other) {
                (ExpressionDomain::Not { operand }, _)
                    if operand.equals(other).as_bool_if_known().unwrap_or(false) =>
                {
                    true.into()
                }
                (_, ExpressionDomain::Not { operand })
                    if operand.equals(self).as_bool_if_known().unwrap_or(false) =>
                {
                    true.into()
                }
                _ => ExpressionDomain::Or {
                    left: box self.clone(),
                    right: box other.clone(),
                },
            }
        }
    }

    /// Returns an expression that is "self % other".
    fn rem(&self, other: &Self) -> Self {
        match (self, other) {
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(val2)),
            ) => {
                let result = f32::from_bits(*val1) % f32::from_bits(*val2);
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(result.to_bits()))
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(val2)),
            ) => {
                let result = f64::from_bits(*val1) % f64::from_bits(*val2);
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(result.to_bits()))
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val2)),
            ) => {
                if *val2 == 0 {
                    ExpressionDomain::Bottom
                } else {
                    ExpressionDomain::CompileTimeConstant(ConstantValue::I128(*val1 % *val2))
                }
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val2)),
            ) => {
                if *val2 == 0 {
                    ExpressionDomain::Bottom
                } else {
                    ExpressionDomain::CompileTimeConstant(ConstantValue::U128(*val1 % *val2))
                }
            }
            _ => ExpressionDomain::Rem {
                left: box self.clone(),
                right: box other.clone(),
            },
        }
    }

    /// Returns an expression that is "self << other".
    fn shl(&self, other: &Self) -> Self {
        let other_as_u32 = match other {
            ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val2)) => Some(*val2 as u32),
            ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val2)) => Some(*val2 as u32),
            _ => None,
        };
        match (self, other_as_u32) {
            (ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1)), Some(val2)) => {
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1.wrapping_shl(val2)))
            }
            (ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1)), Some(val2)) => {
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1.wrapping_shl(val2)))
            }
            _ => ExpressionDomain::Shl {
                left: box self.clone(),
                right: box other.clone(),
            },
        }
    }

    /// Returns an expression that is true if "self << other" is not in range of target_type.
    fn shl_overflows(&self, other: &Self, target_type: ExpressionType) -> Self {
        let other_as_u32 = match other {
            ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val2)) => Some(*val2 as u32),
            ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val2)) => Some(*val2 as u32),
            _ => None,
        };
        match (self, other_as_u32) {
            (ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1)), Some(val2)) => {
                let result = match target_type {
                    ExpressionType::I128 => i128::overflowing_shl(*val1, val2).1,
                    ExpressionType::I64 => i64::overflowing_shl(*val1 as i64, val2).1,
                    ExpressionType::I32 => i32::overflowing_shl(*val1 as i32, val2).1,
                    ExpressionType::I16 => i16::overflowing_shl(*val1 as i16, val2).1,
                    ExpressionType::I8 => i8::overflowing_shl(*val1 as i8, val2).1,
                    _ => unreachable!(),
                };
                result.into()
            }
            (ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1)), Some(val2)) => {
                let result = match target_type {
                    ExpressionType::U128 => u128::overflowing_shl(*val1, val2).1,
                    ExpressionType::U64 => u64::overflowing_shl(*val1 as u64, val2).1,
                    ExpressionType::U32 => u32::overflowing_shl(*val1 as u32, val2).1,
                    ExpressionType::U16 => u16::overflowing_shl(*val1 as u16, val2).1,
                    ExpressionType::U8 => u8::overflowing_shl(*val1 as u8, val2).1,
                    _ => unreachable!(),
                };
                result.into()
            }
            _ => ExpressionDomain::ShlOverflows {
                left: box self.clone(),
                right: box other.clone(),
                result_type: target_type,
            },
        }
    }

    /// Returns an expression that is "self >> other".
    fn shr(&self, other: &Self) -> Self {
        let other_as_u32 = match other {
            ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val2)) => Some(*val2 as u32),
            ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val2)) => Some(*val2 as u32),
            _ => None,
        };
        match (self, other_as_u32) {
            (ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1)), Some(val2)) => {
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1.wrapping_shr(val2)))
            }
            (ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1)), Some(val2)) => {
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1.wrapping_shr(val2)))
            }
            _ => ExpressionDomain::Shr {
                left: box self.clone(),
                right: box other.clone(),
            },
        }
    }

    /// Returns an expression that is true if "self >> other" is not in range of target_type.
    fn shr_overflows(&self, other: &Self, target_type: ExpressionType) -> Self {
        let other_as_u32 = match other {
            ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val2)) => Some(*val2 as u32),
            ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val2)) => Some(*val2 as u32),
            _ => None,
        };
        match (self, other_as_u32) {
            (ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1)), Some(val2)) => {
                let result = match target_type {
                    ExpressionType::I128 => i128::overflowing_shr(*val1, val2).1,
                    ExpressionType::I64 => i64::overflowing_shr(*val1 as i64, val2).1,
                    ExpressionType::I32 => i32::overflowing_shr(*val1 as i32, val2).1,
                    ExpressionType::I16 => i16::overflowing_shr(*val1 as i16, val2).1,
                    ExpressionType::I8 => i8::overflowing_shr(*val1 as i8, val2).1,
                    _ => unreachable!(),
                };
                result.into()
            }
            (ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1)), Some(val2)) => {
                let result = match target_type {
                    ExpressionType::U128 => u128::overflowing_shr(*val1, val2).1,
                    ExpressionType::U64 => u64::overflowing_shr(*val1 as u64, val2).1,
                    ExpressionType::U32 => u32::overflowing_shr(*val1 as u32, val2).1,
                    ExpressionType::U16 => u16::overflowing_shr(*val1 as u16, val2).1,
                    ExpressionType::U8 => u8::overflowing_shr(*val1 as u8, val2).1,
                    _ => unreachable!(),
                };
                result.into()
            }
            _ => ExpressionDomain::ShrOverflows {
                left: box self.clone(),
                right: box other.clone(),
                result_type: target_type,
            },
        }
    }

    /// Returns an expression that is "self - other".
    fn sub(&self, other: &Self) -> Self {
        match (self, other) {
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(val2)),
            ) => {
                let result = f32::from_bits(*val1) - f32::from_bits(*val2);
                ExpressionDomain::CompileTimeConstant(ConstantValue::F32(result.to_bits()))
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(val2)),
            ) => {
                let result = f64::from_bits(*val1) - f64::from_bits(*val2);
                ExpressionDomain::CompileTimeConstant(ConstantValue::F64(result.to_bits()))
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val2)),
            ) => {
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1.wrapping_sub(*val2)))
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val2)),
            ) => {
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1.wrapping_sub(*val2)))
            }
            _ => ExpressionDomain::Sub {
                left: box self.clone(),
                right: box other.clone(),
            },
        }
    }

    /// Returns an expression that is true if "self - other" is not in range of target_type.
    fn sub_overflows(&self, other: &Self, target_type: ExpressionType) -> Self {
        match (self, other) {
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::I128(val2)),
            ) => {
                let result = match target_type {
                    ExpressionType::I128 => i128::overflowing_add(*val1, *val2).1,
                    ExpressionType::I64 => i64::overflowing_add(*val1 as i64, *val2 as i64).1,
                    ExpressionType::I32 => i32::overflowing_add(*val1 as i32, *val2 as i32).1,
                    ExpressionType::I16 => i16::overflowing_add(*val1 as i16, *val2 as i16).1,
                    ExpressionType::I8 => i8::overflowing_add(*val1 as i8, *val2 as i8).1,
                    _ => unreachable!(),
                };
                result.into()
            }
            (
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val1)),
                ExpressionDomain::CompileTimeConstant(ConstantValue::U128(val2)),
            ) => {
                let result = match target_type {
                    ExpressionType::U128 => u128::overflowing_add(*val1, *val2).1,
                    ExpressionType::U64 => u64::overflowing_add(*val1 as u64, *val2 as u64).1,
                    ExpressionType::U32 => u32::overflowing_add(*val1 as u32, *val2 as u32).1,
                    ExpressionType::U16 => u16::overflowing_add(*val1 as u16, *val2 as u16).1,
                    ExpressionType::U8 => u8::overflowing_add(*val1 as u8, *val2 as u8).1,
                    _ => unreachable!(),
                };
                result.into()
            }
            _ => ExpressionDomain::SubOverflows {
                left: box self.clone(),
                right: box other.clone(),
                result_type: target_type,
            },
        }
    }

    /// True if all of the concrete values that correspond to self also correspond to other.
    /// Note: !x.subset(y) does not imply y.subset(x).
    fn subset(&self, other: &Self) -> bool {
        if self == other {
            return true;
        };
        match (self, other) {
            // The empty set is a subset of every other set.
            (ExpressionDomain::Bottom, _) => true,
            // A non empty set is not a subset of the empty set.
            (_, ExpressionDomain::Bottom) => false,
            // Every set is a subset of the universal set.
            (_, ExpressionDomain::Top) => true,
            // The universal set is not a subset of any set other than the universal set.
            (ExpressionDomain::Top, _) => false,
            (
                ExpressionDomain::ConditionalExpression {
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
                ExpressionDomain::ConditionalExpression {
                    consequent,
                    alternate,
                    ..
                },
            ) => {
                // This is a conservative answer. False does not imply other.subset(self).
                self.subset(consequent) && self.subset(alternate)
            }
            // {x} subset {y} iff x = y
            (
                ExpressionDomain::AbstractHeapAddress(a1),
                ExpressionDomain::AbstractHeapAddress(a2),
            ) => a1 == a2,
            (
                ExpressionDomain::CompileTimeConstant(cv1),
                ExpressionDomain::CompileTimeConstant(cv2),
            ) => cv1 == cv2,
            (ExpressionDomain::Reference(p1), ExpressionDomain::Reference(p2)) => p1 == p2,
            // in all other cases we conservatively answer false
            _ => false,
        }
    }

    /// Applies refine_parameters to every domain element and returns the collection of results.
    fn refine_parameters(&self, arguments: &[AbstractValue]) -> ExpressionDomain {
        match self {
            ExpressionDomain::Top
            | ExpressionDomain::Bottom
            | ExpressionDomain::AbstractHeapAddress(..) => self.clone(),
            ExpressionDomain::Add { left, right } => left
                .refine_parameters(arguments)
                .add(&right.refine_parameters(arguments)),
            ExpressionDomain::AddOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_parameters(arguments)
                .add_overflows(&right.refine_parameters(arguments), result_type.clone()),
            ExpressionDomain::And { left, right } => left
                .refine_parameters(arguments)
                .and(&right.refine_parameters(arguments)),
            ExpressionDomain::BitAnd { left, right } => left
                .refine_parameters(arguments)
                .bit_and(&right.refine_parameters(arguments)),
            ExpressionDomain::BitOr { left, right } => left
                .refine_parameters(arguments)
                .bit_or(&right.refine_parameters(arguments)),
            ExpressionDomain::BitXor { left, right } => left
                .refine_parameters(arguments)
                .bit_xor(&right.refine_parameters(arguments)),
            ExpressionDomain::CompileTimeConstant(..) => self.clone(),
            ExpressionDomain::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => consequent.refine_parameters(arguments).join(
                &alternate.refine_parameters(arguments),
                &condition.refine_parameters(arguments),
            ),
            ExpressionDomain::Div { left, right } => left
                .refine_parameters(arguments)
                .div(&right.refine_parameters(arguments)),
            ExpressionDomain::Equals { left, right } => left
                .refine_parameters(arguments)
                .equals(&right.refine_parameters(arguments)),
            ExpressionDomain::GreaterOrEqual { left, right } => left
                .refine_parameters(arguments)
                .ge(&right.refine_parameters(arguments)),
            ExpressionDomain::GreaterThan { left, right } => left
                .refine_parameters(arguments)
                .gt(&right.refine_parameters(arguments)),
            ExpressionDomain::LessOrEqual { left, right } => left
                .refine_parameters(arguments)
                .le(&right.refine_parameters(arguments)),
            ExpressionDomain::LessThan { left, right } => left
                .refine_parameters(arguments)
                .lt(&right.refine_parameters(arguments)),
            ExpressionDomain::Mul { left, right } => left
                .refine_parameters(arguments)
                .mul(&right.refine_parameters(arguments)),
            ExpressionDomain::MulOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_parameters(arguments)
                .mul_overflows(&right.refine_parameters(arguments), result_type.clone()),
            ExpressionDomain::Ne { left, right } => left
                .refine_parameters(arguments)
                .not_equals(&right.refine_parameters(arguments)),
            ExpressionDomain::Neg { operand } => operand.refine_parameters(arguments).neg(),
            ExpressionDomain::Not { operand } => operand.refine_parameters(arguments).not(),
            ExpressionDomain::Offset { left, right } => left
                .refine_parameters(arguments)
                .offset(&right.refine_parameters(arguments)),
            ExpressionDomain::Or { left, right } => left
                .refine_parameters(arguments)
                .or(&right.refine_parameters(arguments)),
            ExpressionDomain::Reference(..) => self.clone(),
            ExpressionDomain::Rem { left, right } => left
                .refine_parameters(arguments)
                .rem(&right.refine_parameters(arguments)),
            ExpressionDomain::Shl { left, right } => left
                .refine_parameters(arguments)
                .shl(&right.refine_parameters(arguments)),
            ExpressionDomain::ShlOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_parameters(arguments)
                .shl_overflows(&right.refine_parameters(arguments), result_type.clone()),
            ExpressionDomain::Shr { left, right } => left
                .refine_parameters(arguments)
                .shr(&right.refine_parameters(arguments)),
            ExpressionDomain::ShrOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_parameters(arguments)
                .shr_overflows(&right.refine_parameters(arguments), result_type.clone()),
            ExpressionDomain::Sub { left, right } => left
                .refine_parameters(arguments)
                .sub(&right.refine_parameters(arguments)),
            ExpressionDomain::SubOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_parameters(arguments)
                .sub_overflows(&right.refine_parameters(arguments), result_type.clone()),
            ExpressionDomain::Variable { path, .. } => match **path {
                Path::LocalVariable { ordinal } if 0 < ordinal && ordinal <= arguments.len() => {
                    arguments[ordinal - 1].value.expression_domain.clone()
                }
                _ => self.clone(),
            },
        }
    }

    /// Returns a domain whose corresponding set of concrete values include all of the values
    /// corresponding to self and other.The set of values may be less precise (more inclusive) than
    /// the set returned by join. The chief requirement is that a small number of widen calls
    /// deterministically lead to Top.
    fn widen(&self, other: &Self, _join_condition: &AbstractDomains) -> Self {
        if self == other {
            return self.clone();
        };
        //todo: #30 don't get to top quite this quickly.
        ExpressionDomain::Top
    }
}
