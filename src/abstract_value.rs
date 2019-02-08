// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//
use abstract_domains::{self, AbstractDomains, ExpressionDomain, ExpressionType};
use constant_value::ConstantValue;
use rustc::hir::def_id::DefId;
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
    /// values resulting from applying "+" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn add(&self, other: &AbstractValue, expression_provenance: Option<Span>) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.add(&other.value),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying add_overflows to each element of the cross product of the concrete
    /// values or self and other.
    pub fn add_overflows(
        &self,
        other: &AbstractValue,
        target_type: ExpressionType,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.add_overflows(&other.value, target_type),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "&&" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn and(&self, other: &AbstractValue, expression_provenance: Option<Span>) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.and(&other.value),
        }
    }

    /// The concrete Boolean value of this abstract value, if known, otherwise None.
    pub fn as_bool_if_known(&self) -> Option<bool> {
        self.value.as_bool_if_known()
    }

    /// If the concrete Boolean value of this abstract value is known, return it as a UI28 constant,
    /// otherwise return None.
    pub fn as_int_if_known(&self) -> Option<AbstractValue> {
        self.as_bool_if_known()
            .map(|b| ConstantValue::U128(b as u128).into())
    }

    /// Returns a list of spans which is the overall span prepended to the concatenation of
    /// the left spans and the right spans.
    fn binary_provenance(overall: Option<Span>, left: &[Span], right: &[Span]) -> Vec<Span> {
        let mut provenance = Vec::new();
        if let Some(expr) = overall {
            provenance.push(expr)
        }
        provenance.extend_from_slice(left);
        provenance.extend_from_slice(right);
        provenance
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "&" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn bit_and(
        &self,
        other: &AbstractValue,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.bit_and(&other.value),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "|" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn bit_or(
        &self,
        other: &AbstractValue,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.bit_or(&other.value),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "^" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn bit_xor(
        &self,
        other: &AbstractValue,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.bit_xor(&other.value),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "/" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn div(&self, other: &AbstractValue, expression_provenance: Option<Span>) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.div(&other.value),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "==" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn equals(
        &self,
        other: &AbstractValue,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.equals(&other.value),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying ">=" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn ge(&self, other: &AbstractValue, expression_provenance: Option<Span>) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.ge(&other.value),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying ">" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn gt(&self, other: &AbstractValue, expression_provenance: Option<Span>) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.gt(&other.value),
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

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "<=" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn le(&self, other: &AbstractValue, expression_provenance: Option<Span>) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.le(&other.value),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "lt" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn lt(&self, other: &AbstractValue, expression_provenance: Option<Span>) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.lt(&other.value),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "*" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn mul(&self, other: &AbstractValue, expression_provenance: Option<Span>) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.mul(&other.value),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying mul_overflows to each element of the cross product of the concrete
    /// values or self and other.
    pub fn mul_overflows(
        &self,
        other: &AbstractValue,
        target_type: ExpressionType,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.mul_overflows(&other.value, target_type),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "!=" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn not_equals(
        &self,
        other: &AbstractValue,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.not_equals(&other.value),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "not" to each element of the concrete values of self.
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
    /// values resulting from applying "ptr.offset" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn offset(
        &self,
        other: &AbstractValue,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.offset(&other.value),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "or" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn or(&self, other: &AbstractValue, expression_provenance: Option<Span>) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.or(&other.value),
        }
    }

    /// Returns a value that is simplified (refined) by using the current path conditions
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

    /// Returns a value that is simplified (refined) by replacing parameter values
    /// with their corresponding argument values. If no refinement is possible
    /// the result is simply a clone of this value.
    pub fn refine_parameters(&self, _arguments: &[AbstractValue]) -> AbstractValue {
        //todo: #60 actually refine this value when values identify parameters.
        self.clone()
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "%" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn rem(&self, other: &AbstractValue, expression_provenance: Option<Span>) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.rem(&other.value),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "<<" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn shl(&self, other: &AbstractValue, expression_provenance: Option<Span>) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.shl(&other.value),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying shl_overflows to each element of the cross product of the concrete
    /// values or self and other.
    pub fn shl_overflows(
        &self,
        other: &AbstractValue,
        target_type: ExpressionType,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.shl_overflows(&other.value, target_type),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying ">>" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn shr(&self, other: &AbstractValue, expression_provenance: Option<Span>) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.shr(&other.value),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying shr_overflows to each element of the cross product of the concrete
    /// values or self and other.
    pub fn shr_overflows(
        &self,
        other: &AbstractValue,
        target_type: ExpressionType,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.shr_overflows(&other.value, target_type),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "-" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn sub(&self, other: &AbstractValue, expression_provenance: Option<Span>) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.sub(&other.value),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying sub_overflows to each element of the cross product of the concrete
    /// values or self and other.
    pub fn sub_overflows(
        &self,
        other: &AbstractValue,
        target_type: ExpressionType,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            value: self.value.sub_overflows(&other.value, target_type),
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
    /// [arg_count ... ] are the local variables and compiler temporaries.
    LocalVariable { ordinal: usize },

    /// The name is a summary cache key string.
    StaticVariable {
        /// The crate specific key that is used to identify the function in the current crate.
        /// This is not available for functions returned by calls to functions from other crates,
        /// since the def id the other crates use have no meaning for the current crate.
        #[serde(skip)]
        def_id: Option<DefId>,
        /// The key to use when retrieving a summary for the static variable from the summary cache.
        summary_cache_key: String,
    },

    /// The ordinal is an index into a method level table of MIR bodies.
    /// This should not be serialized into a summary since it is function private local state.
    PromotedConstant { ordinal: usize },

    /// The qualifier denotes some reference, struct, or collection.
    /// The selector denotes a de-referenced item, field, or element, or slice.
    QualifiedPath {
        qualifier: Box<Path>,
        selector: Box<PathSelector>,
    },
}

impl Path {
    /// True if path qualifies root, or another qualified path rooted by root.
    pub fn is_rooted_by(&self, root: &Path) -> bool {
        match self {
            Path::QualifiedPath { qualifier, .. } => {
                **qualifier == *root || qualifier.is_rooted_by(root)
            }
            _ => false,
        }
    }

    /// Returns a copy path with the root replaced by new_root.
    pub fn replace_root(&self, old_root: &Path, new_root: Path) -> Path {
        match self {
            Path::QualifiedPath {
                qualifier,
                selector,
            } => {
                let new_qualifier = if **qualifier == *old_root {
                    new_root
                } else {
                    qualifier.replace_root(old_root, new_root)
                };
                Path::QualifiedPath {
                    qualifier: box new_qualifier,
                    selector: selector.clone(),
                }
            }
            _ => new_root,
        }
    }
}

/// The selector denotes a de-referenced item, field, or element, or slice.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash)]
pub enum PathSelector {
    /// The length of an array.
    ArrayLength,

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
