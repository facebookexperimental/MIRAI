// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//
use abstract_domains::AbstractDomains;
use rpds::List;

/// Mirai is an abstract interpreter and thus produces abstract values.
/// In general, an abstract value is a value that is not fully known.
/// For example, we may know that it is a number between 1 and 10, but not
/// which particular number.
///
/// When we do know everything about a value, it is concrete rather than
/// abstract, but is convenient to just use this structure for concrete values
/// as well, since all operations can be uniform.
#[derive(Serialize, Deserialize, Debug, Eq, PartialEq, Hash)]
pub struct AbstractValue {
    /// An abstract value is the result of some expression.
    /// The source location of that expression is stored in provence.
    /// When an expression is stored somewhere and then retrieved via an accessor expression, a new
    /// abstract value is created (via refinement using the current path condition) with a provence
    /// that is the source location of accessor expression prepended to the provence of the
    /// refined expression.
    pub provenance: List<Span>,
    /// Various approximations of the actual value.
    /// See https://github.com/facebookexperimental/MIRAI/blob/master/documentation/AbstractValues.md.
    pub value: AbstractDomains,
}

/// Identifies a region of source code that corresponds to a source construct that the
/// analyzer tracks and about which it can generate diagnostic messages.
#[derive(Serialize, Deserialize, Debug, Eq, PartialEq, Hash)]
pub struct Span {
    /// The absolute name of the file containing this source span.
    pub filename: Name,
    /// The number (starting at 1) of the line where this span starts.
    pub start_line: u32,
    /// The number (starting at 1) of the column where this span starts.
    pub start_column: u32,
    /// The number (starting at 1) of the line where this span ends.
    pub end_line: u32,
    /// The number (starting at 1) of the column where this span ends.
    pub end_column: u32,
}

/// The name of a function or method, sufficiently qualified so that it uniquely identifies it
/// among all functions and methods defined in the project corresponding to a summary store.
#[derive(Serialize, Deserialize, Debug, Eq, PartialEq, Hash)]
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
#[derive(Serialize, Deserialize, Debug, Eq, PartialEq, Hash)]
pub enum Path {
    /// The ordinal specifies a local variable or compiler temporary of the current function
    /// For example, in fn foo() { x: i32 = 0; x} we identify variable x with:
    /// Path::LocalVariable { ordinal: 0 }
    LocalVariable {
        ordinal: u32,
    },

    /// The index specifies the position of the parameter in the parameter list of the current function
    /// For example, in fn foo(x: int, y: int) {} we identify parameter x with:
    /// Path::Parameter { index: 0 }
    Parameter {
        index: u32,
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
}
