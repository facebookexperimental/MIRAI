// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//
use abstract_domains::{self, AbstractDomains, ExpressionDomain};
use constant_value::ConstantValue;
use std::fmt::{Debug, Formatter, Result};
use std::hash::{Hash, Hasher};
use syntax_pos::Span;

/// Mirai is an abstract interpreter and thus produces abstract values.
/// In general, an abstract value is a value that is not fully known.
/// For example, we may know that it is a number between 1 and 10, but not
/// which particular number.
///
/// When we do know everything about a value, it is concrete rather than
/// abstract, but is convenient to just use this structure for concrete values
/// as well, since all operations can be uniform.
#[derive(Serialize, Deserialize, Clone)]
pub struct AbstractValue {
    /// An abstract value is the result of some expression.
    /// The source location of that expression is stored in provenance.
    /// When an expression value is stored somewhere and then retrieved via an accessor expression,
    /// a new abstract value is created (via refinement using the current path condition) with a
    /// provenance that is the source location of the accessor expression prepended to the
    /// provenance of the stored value.
    #[serde(skip)]
    pub provenance: Vec<Span>,
    /// Various approximations of the actual value.
    /// See https://github.com/facebookexperimental/MIRAI/blob/master/documentation/AbstractValues.md.
    pub value: AbstractDomains,
}

/// An abstract value that can be used as the value for an operation that has no normal result.
pub const BOTTOM: AbstractValue = AbstractValue {
    provenance: Vec::new(),
    value: abstract_domains::BOTTOM,
};

/// An abstract value that is corresponds to the single concrete value, true.
pub const FALSE: AbstractValue = AbstractValue {
    provenance: Vec::new(),
    value: abstract_domains::FALSE,
};

/// An abstract value to use when nothing is known about the value. All possible concrete values
/// are members of the concrete set of values corresponding to this abstract value.
pub const TOP: AbstractValue = AbstractValue {
    provenance: Vec::new(),
    value: abstract_domains::TOP,
};

/// An abstract value that is corresponds to the single concrete value, true.
pub const TRUE: AbstractValue = AbstractValue {
    provenance: Vec::new(),
    value: abstract_domains::TRUE,
};

impl Debug for AbstractValue {
    fn fmt(&self, f: &mut Formatter) -> Result {
        self.value.fmt(f)
    }
}

impl Eq for AbstractValue {}

impl PartialEq for AbstractValue {
    fn eq(&self, other: &AbstractValue) -> bool {
        self.value.eq(&other.value)
    }
}

impl Hash for AbstractValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state)
    }
}

impl From<ConstantValue> for AbstractValue {
    fn from(cv: ConstantValue) -> AbstractValue {
        AbstractValue {
            provenance: vec![],
            value: AbstractDomains {
                expression_domain: ExpressionDomain::CompileTimeConstant(cv),
            },
        }
    }
}

impl From<ExpressionDomain> for AbstractValue {
    fn from(expression_domain: ExpressionDomain) -> AbstractValue {
        AbstractValue {
            provenance: vec![],
            value: AbstractDomains { expression_domain },
        }
    }
}

impl AbstractValue {
    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "and" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn and(&self, other: &AbstractValue, expression_provenance: Option<Span>) -> AbstractValue {
        let mut provenance = Vec::new();
        if expression_provenance.is_some() {
            provenance.push(expression_provenance.unwrap())
        }
        provenance.extend_from_slice(&self.provenance);
        provenance.extend_from_slice(&other.provenance);
        AbstractValue {
            provenance,
            value: self.value.and(&other.value),
        }
    }

    /// The concrete Boolean value of this abstract value, if known, otherwise None.
    pub fn as_bool_if_known(&self) -> Option<bool> {
        self.value.as_bool_if_known()
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "equals" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn equals(
        &self,
        other: &AbstractValue,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        let mut provenance = Vec::new();
        if expression_provenance.is_some() {
            provenance.push(expression_provenance.unwrap())
        }
        provenance.extend_from_slice(&self.provenance);
        provenance.extend_from_slice(&other.provenance);
        AbstractValue {
            provenance,
            value: self.value.equals(&other.value),
        }
    }

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
        let mut provenance = Vec::new();
        provenance.extend_from_slice(&join_condition.provenance);
        provenance.extend_from_slice(&self.provenance);
        provenance.extend_from_slice(&other.provenance);
        AbstractValue {
            provenance,
            value: self.value.join(&other.value, &join_condition.value),
        }
    }

    pub fn not(&self, expression_provenance: Option<Span>) -> AbstractValue {
        let mut provenance = Vec::new();
        if expression_provenance.is_some() {
            provenance.push(expression_provenance.unwrap())
        }
        provenance.extend_from_slice(&self.provenance);
        AbstractValue {
            provenance,
            value: self.value.not(),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "or" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn or(&self, other: &AbstractValue, expression_provenance: Option<Span>) -> AbstractValue {
        let mut provenance = Vec::new();
        if expression_provenance.is_some() {
            provenance.push(expression_provenance.unwrap())
        }
        provenance.extend_from_slice(&self.provenance);
        provenance.extend_from_slice(&other.provenance);
        AbstractValue {
            provenance,
            value: self.value.or(&other.value),
        }
    }

    /// Returns a value that could be simplified (refined) by using the current path conditions
    /// (conditions known to be true in the current context). If no refinement is possible
    /// the result is simply a clone of this value, but with its provenance updated by
    /// pre-pending the given span.
    pub fn refine_with(&self, _path_condtion: &AbstractValue, provenance: Span) -> AbstractValue {
        //todo: #32 simplify this value using the path condition
        let mut provenance = vec![provenance];
        provenance.extend_from_slice(&self.provenance);
        AbstractValue {
            provenance,
            value: self.value.clone(),
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
            provenance: other.provenance.clone(),
            value: self.value.widen(&other.value, &join_condition.value),
        }
    }

    /// Returns a clone of the value with the given span prepended to its provence.
    pub fn with_provenance(&self, provenance: Span) -> AbstractValue {
        let mut result = self.clone();
        result.provenance.insert(0, provenance);
        result
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
    /// A dynamically allocated memory block.
    AbstractHeapAddress { ordinal: usize },

    /// 0 is the return value temporary
    /// [1 ... arg_count] are the parameters
    /// [arg_count ... ] are the local variables and compiler temporaries
    LocalVariable { ordinal: usize },

    /// The name is a summary cache key string.
    StaticVariable { name: String },

    /// The ordinal is an index into a crate level constant table.
    PromotedConstant { ordinal: usize },

    /// The qualifier denotes some reference, struct, or collection.
    /// The selector denotes a de-referenced item, field, or element, or slice.
    QualifiedPath {
        qualifier: Box<Path>,
        selector: Box<PathSelector>,
    },
}

/// The selector denotes a de-referenced item, field, or element, or slice.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash)]
pub enum PathSelector {
    /// Given a path that denotes a reference, select the thing the reference points to.
    Deref,

    /// Select the struct field with the given index.
    Field(usize),

    /// Select the collection element with the index specified by the abstract value.
    Index(Box<AbstractValue>),

    /// These indices are generated by slice patterns. Easiest to explain
    /// by example:
    ///
    /// ```
    /// [X, _, .._, _, _] => { offset: 0, min_length: 4, from_end: false },
    /// [_, X, .._, _, _] => { offset: 1, min_length: 4, from_end: false },
    /// [_, _, .._, X, _] => { offset: 2, min_length: 4, from_end: true },
    /// [_, _, .._, _, X] => { offset: 1, min_length: 4, from_end: true },
    /// ```
    ConstantIndex {
        /// index or -index (in Python terms), depending on from_end
        offset: u32,
        /// thing being indexed must be at least this long
        min_length: u32,
        /// counting backwards from end?
        from_end: bool,
    },

    /// These indices are generated by slice patterns.
    ///
    /// slice[from:-to] in Python terms.
    Subslice { from: u32, to: u32 },

    /// "Downcast" to a variant of an ADT. Currently, MIR only introduces
    /// this for ADTs with more than one variant. The value is the ordinal of the variant.
    Downcast(usize),
}
