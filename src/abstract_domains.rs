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
    //todo: use cached getters to get other domains on demand
}

/// A collection of abstract domains that all represent the impossible abstract value.
/// I.e. the corresponding set of possible concrete values is empty.
pub const BOTTOM: AbstractDomains = AbstractDomains {
    expression_domain: ExpressionDomain::Bottom,
};

/// A collection of abstract domains that all represent the universal abstract value.
/// I.e. the corresponding set of possible concrete values includes every possible concrete values.
pub const TOP: AbstractDomains = AbstractDomains {
    expression_domain: ExpressionDomain::Top,
};

impl AbstractDomains {
    /// True if all of the abstract domains in this collection correspond to an empty set of concrete values.
    pub fn is_bottom(&self) -> bool {
        self.expression_domain.is_bottom()
    }

    /// True if all of the abstract domains in this collection correspond to the set of all possible concrete values.
    pub fn is_top(&self) -> bool {
        self.expression_domain.is_bottom()
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

    /// Widen all of the abstract domains in the two collections to form a single collection.
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
    /// True if the set of concrete values that correspond to this domain is empty.
    fn is_bottom(&self) -> bool;

    /// True if all possible concrete values are elements of the set corresponding to this domain.
    fn is_top(&self) -> bool;

    /// Returns a domain whose corresponding set of concrete values include all of the values
    /// corresponding to self and other.
    /// In a context where the join condition is known to be true, the result can be refined to be
    /// just self, correspondingly if it is known to be false, the result can be refined to be just other.
    fn join(&self, other: &Self, join_condition: &AbstractDomains) -> Self;

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
/// just one element.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash)]
pub enum ExpressionDomain {
    /// An expression that represents any possible value
    Top,

    /// An expression that represents an impossible value, such as the value returned by function
    /// that always panics.
    Bottom,

    /// An expression that is a compile time constant value, such as a numeric literal or a function.
    CompileTimeConstant(ConstantValue),

    /// An expression that is either if_true or if_false, depending on the value of join_condition.
    JoinedExpression {
        // A condition that results in a Boolean value
        join_condition: Box<AbstractDomains>,
        // The value of this expression if join_condition is true.
        if_true: Box<ExpressionDomain>,
        // The value of this expression if join_condition is false.
        if_false: Box<ExpressionDomain>,
    },
}

impl AbstractDomain for ExpressionDomain {
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
        ExpressionDomain::JoinedExpression {
            join_condition: box join_condition.clone(),
            if_true: box self.clone(),
            if_false: box other.clone(),
        }
    }

    /// Returns a domain whose corresponding set of concrete values include all of the values
    /// corresponding to self and other.The set of values may be less precise (more inclusive) than
    /// the set returned by join. The chief requirement is that a small number of widen calls
    /// deterministically lead to Top.
    fn widen(&self, _other: &Self, _join_condition: &AbstractDomains) -> ExpressionDomain {
        //todo: don't get to top quite this quickly.
        ExpressionDomain::Top
    }

    /// True if all of the concrete values that correspond to self also correspond to other.
    /// Note: !x.subset(y) does not imply y.subset(x).
    fn subset(&self, other: &ExpressionDomain) -> bool {
        match (self, other) {
            // The empty set is a subset of every other set
            (ExpressionDomain::Bottom, _) => true,
            // A non empty set if not a subset of the empty set
            (_, ExpressionDomain::Bottom) => false,
            // Every set is a subset of the universal set
            (_, ExpressionDomain::Top) => true,
            // The universal set is not a subset of any set other than the universal set
            (ExpressionDomain::Top, _) => false,
            (
                ExpressionDomain::JoinedExpression {
                    if_true, if_false, ..
                },
                _,
            ) => {
                // This is a conservative answer. False does not imply other.subset(self).
                if_true.subset(other) && if_false.subset(other)
            }
            (
                _,
                ExpressionDomain::JoinedExpression {
                    if_true, if_false, ..
                },
            ) => {
                // This is a conservative answer. False does not imply other.subset(self).
                self.subset(if_true) || self.subset(if_false)
            }
            // {x} subset {y} iff x = y
            (
                ExpressionDomain::CompileTimeConstant(cv1),
                ExpressionDomain::CompileTimeConstant(cv2),
            ) => cv1 == cv2,
        }
    }
}
