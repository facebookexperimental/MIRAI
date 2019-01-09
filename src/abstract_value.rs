// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//
use abstract_domains::{self, AbstractDomains};
use syntax_pos::Span;

/// Mirai is an abstract interpreter and thus produces abstract values.
/// In general, an abstract value is a value that is not fully known.
/// For example, we may know that it is a number between 1 and 10, but not
/// which particular number.
///
/// When we do know everything about a value, it is concrete rather than
/// abstract, but is convenient to just use this structure for concrete values
/// as well, since all operations can be uniform.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash)]
pub struct AbstractValue {
    /// An abstract value is the result of some expression.
    /// The source location of that expression is stored in provenance.
    /// When an expression is stored somewhere and then retrieved via an accessor expression, a new
    /// abstract value is created (via refinement using the current path condition) with a provenance
    /// that is the source location of accessor expression. If refinement results in an existing
    /// expression (i.e. one with a provenance of its own) then a copy expression is created with
    /// the existing expression as argument, so that both locations are tracked.
    #[serde(skip)]
    pub provenance: Span, //todo: perhaps this should be a list of spans
    /// Various approximations of the actual value.
    /// See https://github.com/facebookexperimental/MIRAI/blob/master/documentation/AbstractValues.md.
    pub value: AbstractDomains,
}

/// An abstract value that can be used as the value for an operation that has no normal result.
pub const BOTTOM: AbstractValue = AbstractValue {
    provenance: syntax_pos::DUMMY_SP,
    value: abstract_domains::BOTTOM,
};

/// An abstract value to use when nothing is known about the value. All possible concrete values
/// are members of the concrete set of values corresponding to this abstract value.
pub const TOP: AbstractValue = AbstractValue {
    provenance: syntax_pos::DUMMY_SP,
    value: abstract_domains::TOP,
};

impl AbstractValue {
    /// True if the set of concrete values that correspond to this abstract value is empty.
    pub fn is_bottom(&self) -> bool {
        self.value.is_bottom()
    }

    /// True if all possible concrete values are elements of the set corresponding to this abstract value.
    pub fn is_top(&self) -> bool {
        self.value.is_top()
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the values
    /// corresponding to self and other.
    /// In a context where the join condition is known to be true, the result can be refined to be
    /// just self, correspondingly if it is known to be false, the result can be refined to be just other.
    pub fn join(&self, other: &AbstractValue, join_condition: &AbstractValue) -> AbstractValue {
        AbstractValue {
            provenance: syntax_pos::DUMMY_SP,
            value: self.value.join(&other.value, &join_condition.value),
        }
    }

    /// True if all of the concrete values that correspond to self also correspond to other.
    pub fn subset(&self, other: &AbstractValue) -> bool {
        self.value.subset(&other.value)
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the values
    /// corresponding to self and other. The set of values may be less precise (more inclusive) than
    /// the set returned by join. The chief requirement is that a small number of widen calls
    /// deterministically lead to Top.
    pub fn widen(&self, other: &AbstractValue, join_condition: &AbstractValue) -> AbstractValue {
        AbstractValue {
            provenance: syntax_pos::DUMMY_SP,
            value: self.value.widen(&other.value, &join_condition.value),
        }
    }
}

/// The name of a function or method, sufficiently qualified so that it uniquely identifies it
/// among all functions and methods defined in the project corresponding to a summary store.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash)]
pub enum Name {
    /// A root name in the current name space. Typically the name of a crate, used module, or
    /// used function or struct/trait/enum/type.
    Root { identifier: String },

    /// A name that selects a named component (specified by selector) of the structure named by the
    /// qualifier.
    QualifiedName {
        qualifier: Box<Name>,
        selector: String,
    },
}

/// A path represents a left hand side expression.
/// When the actual expression is evaluated at runtime it will resolve to a particular memory
/// location. During analysis it is used to keep track of state changes.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash)]
pub enum Path {
    /// The ordinal specifies a local variable or compiler temporary of the current function
    /// For example, in fn foo() { x: i32 = 0; x} we identify variable x with:
    /// Path::LocalVariable { ordinal: 0 }
    LocalVariable {
        ordinal: usize,
    },

    /// The index specifies the position of the parameter in the parameter list of the current function
    /// For example, in fn foo(x: int, y: int) {} we identify parameter x with:
    /// Path::Parameter { index: 0 }
    Parameter {
        index: usize,
    },

    // The name uniquely identifies a static field within the current crate.
    // For example, in mod m { static x: int = 0; } we identify static field x with:
    // Path::StaticRoot {
    //     name: Name {
    //         qualifier: Name::Root {
    //             identifier: String::from("m")
    //         },
    //        selector: String::from("x")
    //     }
    // }
    StaticRoot {
        name: Name,
    },

    /// The identifier denotes a field in the struct found at the path in qualifier.
    /// For example, in struct A { f: i32 }; fn f(x: A) { x.f }, we identify x.f with
    /// Path::QualifiedName { qualifier: Path::Parameter { offset: 0 }, selector: String::from("f") }
    QualifiedName {
        qualifier: Box<Path>,
        selector: String,
    },

    /// The index denotes an element of a collection found at the path in qualifier.
    /// For example, in fn f(x: [A]) { x[0] }, we identify x[0] with
    /// Path::QualifiedIndex {
    ///     qualifier: Path::Parameter { offset: 0 },
    ///     index: box AbstractValue { /*for const 0*/ }
    /// }
    QualifiedIndex {
        qualifier: Box<Path>,
        index: Box<AbstractValue>,
    },
    //todo: need a path for a conditional CFG link
}
