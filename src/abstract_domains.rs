// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use constant_value::ConstantValue;

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
    /// Applies "and" to every pair of domain elements and returns the collection of results.
    pub fn and(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.and(&other.expression_domain),
        }
    }

    /// Applies "equals" to every pair of domain elements and returns the collection of results.
    pub fn equals(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.equals(&other.expression_domain),
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

    /// Applies "not" to every domain element and returns the collection of results.
    pub fn not(&self) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.not(),
        }
    }

    /// Applies "or" to every pair of domain elements and returns the collection of results.
    pub fn or(&self, other: &AbstractDomains) -> AbstractDomains {
        AbstractDomains {
            expression_domain: self.expression_domain.or(&other.expression_domain),
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
    /// mapping the concrete "and" operation over the elements of the cross product of self and other.
    fn and(&self, other: &Self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "equals" operation over the elements of the cross product of self and other.
    fn equals(&self, other: &Self) -> Self;

    /// True if the set of concrete values that correspond to this domain is empty.
    fn is_bottom(&self) -> bool;

    /// True if all possible concrete values are elements of the set corresponding to this domain.
    fn is_top(&self) -> bool;

    /// Returns a domain whose corresponding set of concrete values include all of the values
    /// corresponding to self and other.
    /// In a context where the join condition is known to be true, the result can be refined to be
    /// just self, correspondingly if it is known to be false, the result can be refined to be just other.
    fn join(&self, other: &Self, join_condition: &AbstractDomains) -> Self;

    /// True if the domain corresponds to the concrete set { false }
    fn must_be_false(&self) -> bool;

    /// True if the domain corresponds to the concrete set { true }
    fn must_be_true(&self) -> bool;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "not" operation over the elements of self.
    fn not(&self) -> Self;

    /// Returns a domain whose concrete set is a superset of the set of values resulting from
    /// mapping the concrete "or" operation over the elements of the cross product of self and other.
    fn or(&self, other: &Self) -> Self;

    /// True if all of the concrete values that correspond to self also correspond to other.
    fn subset(&self, other: &Self) -> bool;

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

    // An expression that is true if both left and right are true.
    And {
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

    // An expression that is true if left and right are equal.
    Equals {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },

    /// An expression that is true if the operand is false.
    Not { operand: Box<ExpressionDomain> },

    // An expression that is true if either one of left or right are true.
    Or {
        // The value of the left operand.
        left: Box<ExpressionDomain>,
        // The value of the right operand.
        right: Box<ExpressionDomain>,
    },
}

impl AbstractDomain for ExpressionDomain {
    /// Returns an expression that is "self && other".
    fn and(&self, other: &Self) -> Self {
        if self.must_be_true() {
            if other.must_be_true() {
                ExpressionDomain::CompileTimeConstant(ConstantValue::True)
            } else {
                other.clone()
            }
        } else if other.must_be_true() {
            self.clone()
        } else {
            // todo: #32 more simplifications
            ExpressionDomain::And {
                left: box self.clone(),
                right: box other.clone(),
            }
        }
    }

    /// Returns an expression that is "self == other".
    fn equals(&self, other: &Self) -> Self {
        match (self, other) {
            (
                ExpressionDomain::CompileTimeConstant(cv1),
                ExpressionDomain::CompileTimeConstant(cv2),
            ) => {
                if cv1 == cv2 {
                    ExpressionDomain::CompileTimeConstant(ConstantValue::True)
                } else {
                    ExpressionDomain::CompileTimeConstant(ConstantValue::False)
                }
            }
            _ => ExpressionDomain::Equals {
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
    fn join(&self, other: &ExpressionDomain, join_condition: &AbstractDomains) -> ExpressionDomain {
        ExpressionDomain::ConditionalExpression {
            condition: box join_condition.clone(),
            consequent: box self.clone(),
            alternate: box other.clone(),
        }
    }

    /// True if this expression is known at compile time to be false.
    fn must_be_false(&self) -> bool {
        match self {
            ExpressionDomain::CompileTimeConstant(ConstantValue::False) => true,
            _ => false,
        }
    }

    /// True if this expression is known at compile time to be true.
    fn must_be_true(&self) -> bool {
        match self {
            ExpressionDomain::CompileTimeConstant(ConstantValue::True) => true,
            _ => false,
        }
    }

    /// Returns an expression that is "!self".
    fn not(&self) -> Self {
        match self {
            ExpressionDomain::CompileTimeConstant(ConstantValue::False) => {
                ExpressionDomain::CompileTimeConstant(ConstantValue::True)
            }
            ExpressionDomain::CompileTimeConstant(ConstantValue::True) => {
                ExpressionDomain::CompileTimeConstant(ConstantValue::False)
            }
            _ => ExpressionDomain::Not {
                operand: box self.clone(),
            },
        }
    }

    /// Returns an expression that is "self || other".
    fn or(&self, other: &ExpressionDomain) -> ExpressionDomain {
        if self.must_be_true() || other.must_be_true() {
            ExpressionDomain::CompileTimeConstant(ConstantValue::True)
        } else if self.must_be_false() {
            other.clone()
        } else if other.must_be_false() {
            self.clone()
        } else {
            // todo: #32 more simplifications
            ExpressionDomain::Or {
                left: box self.clone(),
                right: box other.clone(),
            }
        }
    }

    /// True if all of the concrete values that correspond to self also correspond to other.
    /// Note: !x.subset(y) does not imply y.subset(x).
    fn subset(&self, other: &ExpressionDomain) -> bool {
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
            (
                _,
                ExpressionDomain::ConditionalExpression {
                    consequent,
                    alternate,
                    ..
                },
            ) => {
                // This is a conservative answer. False does not imply other.subset(self).
                self.subset(consequent) || self.subset(alternate)
            }
            // {x} subset {y} iff x = y
            (
                ExpressionDomain::CompileTimeConstant(cv1),
                ExpressionDomain::CompileTimeConstant(cv2),
            ) => cv1 == cv2,
            // in all other cases we conservatively answer false
            _ => false,
        }
    }

    /// Returns a domain whose corresponding set of concrete values include all of the values
    /// corresponding to self and other.The set of values may be less precise (more inclusive) than
    /// the set returned by join. The chief requirement is that a small number of widen calls
    /// deterministically lead to Top.
    fn widen(&self, _other: &Self, _join_condition: &AbstractDomains) -> ExpressionDomain {
        //todo: #30 don't get to top quite this quickly.
        ExpressionDomain::Top
    }
}
