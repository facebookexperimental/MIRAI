// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//
use crate::abstract_domains::{self, AbstractDomain};
use crate::constant_domain::ConstantDomain;
use crate::environment::Environment;
use crate::expression::{Expression, ExpressionType};

use log::debug;
use mirai_annotations::assume;
use rustc::hir::def_id::DefId;
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
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
#[derive(Serialize, Deserialize, Clone, Ord, PartialOrd)]
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
    pub domain: AbstractDomain,
}

/// An abstract value that can be used as the value for an operation that has no normal result.
pub const BOTTOM: AbstractValue = AbstractValue {
    provenance: Vec::new(),
    domain: abstract_domains::BOTTOM,
};

/// An abstract value that is corresponds to the single concrete value, true.
pub const FALSE: AbstractValue = AbstractValue {
    provenance: Vec::new(),
    domain: abstract_domains::FALSE,
};

/// An abstract value to use when nothing is known about the value. All possible concrete values
/// are members of the concrete set of values corresponding to this abstract value.
pub const TOP: AbstractValue = AbstractValue {
    provenance: Vec::new(),
    domain: abstract_domains::TOP,
};

/// An abstract value that is corresponds to the single concrete value, true.
pub const TRUE: AbstractValue = AbstractValue {
    provenance: Vec::new(),
    domain: abstract_domains::TRUE,
};

impl Debug for AbstractValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.domain.fmt(f)
    }
}

impl Eq for AbstractValue {}

impl PartialEq for AbstractValue {
    fn eq(&self, other: &AbstractValue) -> bool {
        self.domain.eq(&other.domain)
    }
}

impl Hash for AbstractValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.domain.hash(state)
    }
}

impl From<ConstantDomain> for AbstractValue {
    fn from(cv: ConstantDomain) -> AbstractValue {
        AbstractValue {
            provenance: vec![],
            domain: Expression::CompileTimeConstant(cv).into(),
        }
    }
}

impl From<Expression> for AbstractValue {
    fn from(expression_domain: Expression) -> AbstractValue {
        AbstractValue {
            provenance: vec![],
            domain: expression_domain.into(),
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
            domain: self.domain.add(&other.domain),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying add_overflows to each element of the cross product of the concrete
    /// values or self and other.
    pub fn add_overflows(
        &mut self,
        other: &mut AbstractValue,
        target_type: ExpressionType,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            domain: (&mut self.domain).add_overflows(&mut other.domain, target_type),
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
            domain: self.domain.and(&other.domain),
        }
    }

    /// The concrete Boolean value of this abstract value, if known, otherwise None.
    pub fn as_bool_if_known(&self) -> Option<bool> {
        self.domain.as_bool_if_known()
    }

    /// If the concrete Boolean value of this abstract value is known, return it as a UI28 constant,
    /// otherwise return None.
    pub fn as_int_if_known(&self) -> Option<AbstractValue> {
        self.as_bool_if_known()
            .map(|b| ConstantDomain::U128(b as u128).into())
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
            domain: self.domain.bit_and(&other.domain),
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
            domain: self.domain.bit_or(&other.domain),
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
            domain: self.domain.bit_xor(&other.domain),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "as target_type" to each element of the concrete values of self.
    pub fn cast(&self, target_type: ExpressionType) -> AbstractValue {
        AbstractValue {
            provenance: self.provenance.clone(),
            domain: self.domain.cast(target_type),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the values
    /// corresponding to self and other.
    /// In a context where the condition is known to be true, the result can be refined to be
    /// just self, correspondingly if it is known to be false, the result can be refined to be just other.
    pub fn conditional_expression(
        &self,
        consequent: &AbstractValue,
        alternate: &AbstractValue,
    ) -> AbstractValue {
        let mut provenance = Vec::new();
        provenance.extend_from_slice(&self.provenance);
        provenance.extend_from_slice(&consequent.provenance);
        provenance.extend_from_slice(&alternate.provenance);
        AbstractValue {
            provenance,
            domain: self
                .domain
                .conditional_expression(&consequent.domain, &alternate.domain),
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
            domain: self.domain.div(&other.domain),
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
            domain: self.domain.equals(&other.domain),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying ">=" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn greater_or_equal(
        &mut self,
        other: &mut AbstractValue,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            domain: self.domain.greater_or_equal(&mut other.domain),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying ">" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn greater_than(
        &mut self,
        other: &mut AbstractValue,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            domain: self.domain.greater_than(&mut other.domain),
        }
    }

    pub fn implies(&self, other: &AbstractValue) -> bool {
        self.domain.implies(&other.domain)
    }

    /// True if the set of concrete values that correspond to this abstract value is empty.
    pub fn is_bottom(&self) -> bool {
        self.domain.is_bottom()
    }

    /// True if all possible concrete values are elements of the set corresponding to this abstract value.
    pub fn is_top(&self) -> bool {
        self.domain.is_top()
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the values
    /// corresponding to self and other.
    /// In a context where the join condition is known to be true, the result can be refined to be
    /// just self, correspondingly if it is known to be false, the result can be refined to be just other.
    pub fn join(&self, other: &AbstractValue, path: &Path) -> AbstractValue {
        let mut provenance = Vec::new();
        provenance.extend_from_slice(&self.provenance);
        provenance.extend_from_slice(&other.provenance);
        AbstractValue {
            provenance,
            domain: self.domain.join(&other.domain, path),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "<=" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn less_or_equal(
        &mut self,
        other: &mut AbstractValue,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            domain: self.domain.less_or_equal(&mut other.domain),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "lt" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn less_than(
        &mut self,
        other: &mut AbstractValue,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            domain: self.domain.less_than(&mut other.domain),
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
            domain: self.domain.mul(&other.domain),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying mul_overflows to each element of the cross product of the concrete
    /// values or self and other.
    pub fn mul_overflows(
        &mut self,
        other: &mut AbstractValue,
        target_type: ExpressionType,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            domain: self.domain.mul_overflows(&mut other.domain, target_type),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying "neg" to each element of the concrete values of self.
    pub fn neg(&self, expression_provenance: Option<Span>) -> AbstractValue {
        let mut provenance = Vec::new();
        if expression_provenance.is_some() {
            provenance.push(expression_provenance.unwrap())
        }
        provenance.extend_from_slice(&self.provenance);
        AbstractValue {
            provenance,
            domain: self.domain.neg(),
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
            domain: self.domain.not_equals(&other.domain),
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
            domain: self.domain.not(),
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
            domain: self.domain.offset(&other.domain),
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
            domain: self.domain.or(&other.domain),
        }
    }

    /// Adds any abstract heap addresses found in the associated expression to the given set.
    pub fn record_heap_addresses(&self, result: &mut HashSet<usize>) {
        self.domain.expression.record_heap_addresses(result);
    }

    /// Returns a value that is simplified (refined) by using the current path conditions
    /// (conditions known to be true in the current context). If no refinement is possible
    /// the result is simply a clone of this value, but with its provenance updated by
    /// pre-pending the given span.
    pub fn refine_with(&self, path_condition: &AbstractValue, provenance: Span) -> AbstractValue {
        let mut provenance = vec![provenance];
        provenance.extend_from_slice(&self.provenance);
        AbstractValue {
            provenance,
            domain: self.domain.refine_with(&path_condition.domain, 0),
        }
    }

    /// Returns a value that is simplified (refined) by replacing values with Variable(path) expressions
    /// with the value at that path (if there is one). If no refinement is possible
    /// the result is simply a clone of this value. This refinement only makes sense
    /// following a call to refine_parameters.
    pub fn refine_paths(&self, environment: &mut Environment) -> AbstractValue {
        AbstractValue {
            provenance: self.provenance.clone(),
            domain: self.domain.refine_paths(environment),
        }
    }

    /// Returns a value that is simplified (refined) by replacing parameter values
    /// with their corresponding argument values. If no refinement is possible
    /// the result is simply a clone of this value.
    pub fn refine_parameters(&self, arguments: &[(Path, AbstractValue)]) -> AbstractValue {
        AbstractValue {
            provenance: self.provenance.clone(),
            domain: self.domain.refine_parameters(arguments),
        }
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
            domain: self.domain.rem(&other.domain),
        }
    }

    /// Returns a clone of the value with the given span replacing its provenance.
    pub fn replacing_provenance(&self, provenance: Span) -> AbstractValue {
        let mut result = self.clone();
        result.provenance = vec![provenance];
        result
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
            domain: self.domain.shl(&other.domain),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying shl_overflows to each element of the cross product of the concrete
    /// values or self and other.
    pub fn shl_overflows(
        &self,
        other: &mut AbstractValue,
        target_type: ExpressionType,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            domain: self.domain.shl_overflows(&mut other.domain, target_type),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying ">>" to each element of the cross product of the concrete
    /// values or self and other.
    pub fn shr(
        &self,
        other: &AbstractValue,
        expression_type: ExpressionType,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            domain: self.domain.shr(&other.domain, expression_type),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying shr_overflows to each element of the cross product of the concrete
    /// values or self and other.
    pub fn shr_overflows(
        &self,
        other: &mut AbstractValue,
        target_type: ExpressionType,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            domain: self.domain.shr_overflows(&mut other.domain, target_type),
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
            domain: self.domain.sub(&other.domain),
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the
    /// values resulting from applying sub_overflows to each element of the cross product of the concrete
    /// values or self and other.
    pub fn sub_overflows(
        &mut self,
        other: &mut AbstractValue,
        target_type: ExpressionType,
        expression_provenance: Option<Span>,
    ) -> AbstractValue {
        AbstractValue {
            provenance: Self::binary_provenance(
                expression_provenance,
                &self.provenance,
                &other.provenance,
            ),
            domain: self.domain.sub_overflows(&mut other.domain, target_type),
        }
    }

    /// True if all of the concrete values that correspond to self also correspond to other.
    pub fn subset(&self, other: &AbstractValue) -> bool {
        self.domain.subset(&other.domain)
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the values
    /// corresponding to self and other. The set of values may be less precise (more inclusive) than
    /// the set returned by join. The chief requirement is that a small number of widen calls
    /// deterministically lead to Top.
    pub fn widen(&self, path: &Path) -> AbstractValue {
        AbstractValue {
            provenance: self.provenance.clone(),
            domain: self.domain.widen(path),
        }
    }

    /// Returns a clone of the value with the given span prepended to its provenance.
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
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Path {
    /// A dynamically allocated memory block.
    AbstractHeapAddress { ordinal: usize },

    /// Sometimes a constant value needs to be treated as a path during refinement.
    /// Don't use this unless you are really sure you know what you are doing.
    Constant { value: Box<AbstractValue> },

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
        /// The type to use when the static variable value is not yet available.
        expression_type: ExpressionType,
    },

    /// The ordinal is an index into a method level table of MIR bodies.
    /// This should not be serialized into a summary since it is function private local state.
    PromotedConstant { ordinal: usize },

    /// The qualifier denotes some reference, struct, or collection.
    /// The selector denotes a de-referenced item, field, or element, or slice.
    QualifiedPath {
        length: usize,
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

    // Returns the length of the path.
    pub fn path_length(&self) -> usize {
        match self {
            Path::QualifiedPath { length, .. } => *length,
            _ => 1,
        }
    }

    /// Adds any abstract heap addresses found in embedded index values to the given set.
    pub fn record_heap_addresses(&self, result: &mut HashSet<usize>) {
        if let Path::QualifiedPath {
            qualifier,
            selector,
            ..
        } = self
        {
            (**qualifier).record_heap_addresses(result);
            selector.record_heap_addresses(result);
        }
    }

    /// Refine parameters inside embedded index values with the given arguments.
    pub fn refine_parameters(&self, arguments: &[(Path, AbstractValue)]) -> Path {
        match self {
            Path::LocalVariable { ordinal } if 0 < *ordinal && *ordinal <= arguments.len() => {
                arguments[*ordinal - 1].0.clone()
            }
            Path::QualifiedPath {
                ref qualifier,
                ref selector,
                ..
            } => {
                let refined_qualifier = qualifier.refine_parameters(arguments);
                let refined_selector = selector.refine_parameters(arguments);
                let refined_length = refined_qualifier.path_length();
                assume!(refined_length < 1_000_000_000); // We'll run out of memory long before this happens
                Path::QualifiedPath {
                    qualifier: box refined_qualifier,
                    selector: box refined_selector,
                    length: refined_length + 1,
                }
            }
            _ => self.clone(),
        }
    }

    /// Refine paths that reference other paths.
    /// I.e. when a reference is passed to a function that then returns
    /// or leaks it back to the caller in the qualifier of a path then
    /// we want to dereference the qualifier in order to normalize the path
    /// and not have more than one path for the same location.
    pub fn refine_paths(&self, environment: &mut Environment) -> Self {
        if let Path::QualifiedPath {
            qualifier,
            selector,
            ..
        } = self
        {
            if let Some(val) = environment.value_at(&**qualifier) {
                match &val.domain.expression {
                    Expression::Reference(ref dereferenced_path) => {
                        // The qualifier is being dereferenced, so if the value at qualifier
                        // is an explicit reference to another path, put the other path in the place
                        // of qualifier since references do not own elements directly in
                        // the environment.
                        //
                        // If the new qualifier is itself a reference, we have to dereference again.
                        let qualifier = dereferenced_path.clone().refine_paths(environment);
                        let path_len = qualifier.path_length();
                        assume!(path_len < 1_000_000_000); // We'll run out of memory long before this happens
                        return Path::QualifiedPath {
                            qualifier: box qualifier,
                            selector: selector.clone(),
                            length: path_len + 1,
                        };
                    }
                    // if **path == **qualifier, this value came about as the result of a copy
                    // sequence that started in a formal parameter.
                    Expression::Variable { ref path, .. } if (**path != **qualifier) => {
                        // In this case the qualifier is not a reference, but an alias created by
                        // by a move instruction.
                        // Normally, when local a is assigned to local b, all of the
                        // paths rooted in a are copied or moved to paths rooted in b.
                        // In the case of formal parameters, however, there are no paths to
                        // copy or move and instead the target is assigned a value which, in the case
                        // of a move, is in an alias to the parameter. We de-alias here, which is
                        // needed because ultimately the path has to get refined (again) in a calling
                        // context where the root has to be the parameter.
                        //
                        // If the new qualifier is itself an alias we have to de-alias again.
                        let qualifier = path.clone().refine_paths(environment);
                        let path_len = qualifier.path_length();
                        assume!(path_len < 1_000_000_000); // We'll run out of memory long before this happens
                        return Path::QualifiedPath {
                            qualifier: box qualifier,
                            selector: selector.clone(),
                            length: path_len + 1,
                        };
                    }
                    Expression::CompileTimeConstant(constant_value) => {
                        debug!("constant qualifier with path selector that is not in the environment\n{:?}\n{:?}\n{:?}", constant_value, self, environment);
                        //todo: at least some of these arise from qualifiers that are ADTs
                    }
                    _ => {
                        // Although the qualifier matches an expression, that expression
                        // is too abstract too qualify the path sufficiently that we
                        // can refine this value.
                    }
                }
            } else {
                // The qualifier does not match a value in the environment, but parts of it might.
                // Reminder, a path that does not match a value in the environment is rooted in
                // an unknown value, such as a parameter.
                let refined_qualifier = qualifier.refine_paths(environment);
                let refined_selector = selector.refine_paths(environment);
                let refined_length = refined_qualifier.path_length();
                assume!(refined_length < 1_000_000_000); // We'll run out of memory long before this happens
                return Path::QualifiedPath {
                    qualifier: box refined_qualifier,
                    selector: box refined_selector,
                    length: refined_length + 1,
                };
            }
        }
        self.clone()
    }

    /// Returns a copy path with the root replaced by new_root.
    pub fn replace_root(&self, old_root: &Path, new_root: Path) -> Path {
        match self {
            Path::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                let new_qualifier = if **qualifier == *old_root {
                    new_root
                } else {
                    qualifier.replace_root(old_root, new_root)
                };
                assume!(new_qualifier.path_length() < 1_000_000_000); // We'll run out of memory long before this happens
                Path::QualifiedPath {
                    length: new_qualifier.path_length() + 1,
                    qualifier: box new_qualifier,
                    selector: selector.clone(),
                }
            }
            _ => new_root,
        }
    }
}

/// The selector denotes a de-referenced item, field, or element, or slice.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
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

impl PathSelector {
    /// Adds any abstract heap addresses found in embedded index values to the given set.
    pub fn record_heap_addresses(&self, result: &mut HashSet<usize>) {
        if let PathSelector::Index(boxed_abstract_value) = self {
            boxed_abstract_value.record_heap_addresses(result);
        }
    }

    /// Returns a value that is simplified (refined) by replacing values with Variable(path) expressions
    /// with the value at that path (if there is one). If no refinement is possible
    /// the result is simply a clone of this value. This refinement only makes sense
    /// following a call to refine_parameters.
    pub fn refine_paths(&self, environment: &mut Environment) -> Self {
        if let PathSelector::Index(boxed_abstract_value) = self {
            let refined_value = (**boxed_abstract_value).refine_paths(environment);
            PathSelector::Index(box refined_value)
        } else {
            self.clone()
        }
    }

    /// Refine parameters inside embedded index values with the given arguments.
    pub fn refine_parameters(&self, arguments: &[(Path, AbstractValue)]) -> Self {
        if let PathSelector::Index(boxed_abstract_value) = self {
            let refined_value = (**boxed_abstract_value).refine_parameters(arguments);
            PathSelector::Index(box refined_value)
        } else {
            self.clone()
        }
    }
}
