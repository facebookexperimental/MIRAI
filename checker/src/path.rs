// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//
use crate::abstract_value::AbstractValue;
use crate::abstract_value::AbstractValueTrait;
use crate::constant_domain::ConstantDomain;
use crate::environment::Environment;
use crate::expression::{Expression, ExpressionType};
use crate::k_limits;

use log_derive::*;
use mirai_annotations::*;
use rustc_hir::def_id::DefId;
use serde::{Deserialize, Serialize};
use std::collections::hash_map::DefaultHasher;
use std::collections::HashSet;
use std::fmt::{Debug, Formatter, Result};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

/// During join and widen operations, paths are copied from one environment to another, causing them
/// to get rehashed. This turns out to be expensive, so for this case we cache the hash to avoid
/// recomputing it. The caching has a cost, so only use this in cases where it is highly likely
/// that the path will be hashed more than once.
#[derive(Serialize, Deserialize, Clone, Eq, Ord, PartialOrd)]
pub struct Path {
    pub value: PathEnum,
    hash: u64,
}

impl Debug for Path {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.value.fmt(f)
    }
}

impl Hash for Path {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash);
    }
}

impl PartialEq for Path {
    fn eq(&self, other: &Path) -> bool {
        self.hash == other.hash && self.value == other.value
    }
}

impl From<PathEnum> for Path {
    #[logfn_inputs(TRACE)]
    fn from(value: PathEnum) -> Self {
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        Path {
            value,
            hash: hasher.finish(),
        }
    }
}

impl Path {
    /// Returns a qualified path of the form root.selectors[0].selectors[1]...
    #[logfn_inputs(TRACE)]
    pub fn add_selectors(root: &Rc<Path>, selectors: &[Rc<PathSelector>]) -> Rc<Path> {
        let mut result = root.clone();
        for selector in selectors.iter() {
            result = Path::new_qualified(result, selector.clone());
        }
        result
    }

    /// Requires an abstract value that is an AbstractHeapAddress expression and
    /// returns a path can be used as the root of paths that define the heap value.
    #[logfn_inputs(TRACE)]
    pub fn get_as_path(value: Rc<AbstractValue>) -> Path {
        precondition!(matches!(value.expression, Expression::HeapBlock {..}));
        match &value.expression {
            Expression::HeapBlock { .. } => PathEnum::HeapBlock { value }.into(),
            Expression::Offset { .. } => PathEnum::Offset { value }.into(),
            Expression::Reference(path)
            | Expression::Variable { path, .. }
            | Expression::Widen { path, .. } => path.as_ref().clone(),
            _ => verify_unreachable!(),
        }
    }
}

/// A path represents a left hand side expression.
/// When the actual expression is evaluated at runtime it will resolve to a particular memory
/// location. During analysis it is used to keep track of state changes.
#[derive(Serialize, Deserialize, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum PathEnum {
    /// Sometimes a constant value needs to be treated as a path during refinement.
    /// Don't use this unless you are really sure you know what you are doing.
    Constant { value: Rc<AbstractValue> },

    /// A dynamically allocated memory block.
    HeapBlock { value: Rc<AbstractValue> },

    /// locals [arg_count+1..] are the local variables and compiler temporaries.
    LocalVariable { ordinal: usize },

    /// An offset into a memory block
    Offset { value: Rc<AbstractValue> },

    /// locals [1..=arg_count] are the parameters
    Parameter { ordinal: usize },

    /// local 0 is the return value temporary
    Result,

    /// The name is a summary cache key string.
    StaticVariable {
        /// The crate specific key that is used to identify the function in the current crate.
        /// This is not available for functions returned by calls to functions from other crates,
        /// since the def id the other crates use have no meaning for the current crate.
        #[serde(skip)]
        def_id: Option<DefId>,
        /// The key to use when retrieving a summary for the static variable from the summary cache.
        summary_cache_key: Rc<String>,
        /// The type to use when the static variable value is not yet available.
        expression_type: ExpressionType,
    },

    /// This path points to data that is not used, but exists only to satisfy a static checker
    /// that a generic parameter is actually used.
    PhantomData,

    /// The ordinal is an index into a method level table of MIR bodies.
    /// This should not be serialized into a summary since it is function private local state.
    PromotedConstant { ordinal: usize },

    /// The qualifier denotes some reference, struct, or collection.
    /// The selector denotes a de-referenced item, field, or element, or slice.
    QualifiedPath {
        length: usize,
        qualifier: Rc<Path>,
        selector: Rc<PathSelector>,
    },
}

impl Debug for PathEnum {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            PathEnum::Constant { value } => value.fmt(f),
            PathEnum::HeapBlock { value } => f.write_fmt(format_args!("<{:?}>", value)),
            PathEnum::LocalVariable { ordinal } => f.write_fmt(format_args!("local_{}", ordinal)),
            PathEnum::Offset { value } => f.write_fmt(format_args!("<{:?}>", value)),
            PathEnum::Parameter { ordinal } => f.write_fmt(format_args!("param_{}", ordinal)),
            PathEnum::Result => f.write_str("result"),
            PathEnum::StaticVariable {
                summary_cache_key, ..
            } => summary_cache_key.fmt(f),
            PathEnum::PhantomData => f.write_str("phantom_data"),
            PathEnum::PromotedConstant { ordinal } => {
                f.write_fmt(format_args!("constant_{}", ordinal))
            }
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } => f.write_fmt(format_args!("{:?}.{:?}", qualifier, selector)),
        }
    }
}

impl Path {
    /// True if path qualifies root, or another qualified path rooted by root,
    /// by selecting field 0.
    #[logfn_inputs(TRACE)]
    pub fn is_first_leaf_rooted_in(&self, root: &Rc<Path>) -> bool {
        match &self.value {
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                if let PathSelector::Field(0) = *selector.as_ref() {
                    *qualifier == *root || qualifier.is_first_leaf_rooted_in(root)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    /// True if path is, or is rooted by local variable 0, which is reserved for the function result.
    #[logfn_inputs(TRACE)]
    pub fn is_result_or_is_rooted_by_result(&self) -> bool {
        match &self.value {
            PathEnum::QualifiedPath { qualifier, .. } => {
                qualifier.is_result_or_is_rooted_by_result()
            }
            PathEnum::Result => true,
            _ => false,
        }
    }

    /// True if path qualifies root, or another qualified path rooted by root.
    #[logfn_inputs(TRACE)]
    pub fn is_rooted_by(&self, root: &Rc<Path>) -> bool {
        match &self.value {
            PathEnum::QualifiedPath { qualifier, .. } => {
                *qualifier == *root || qualifier.is_rooted_by(root)
            }
            _ => false,
        }
    }

    /// True if path qualifies an abstract heap block, or another qualified path rooted by an
    /// abstract heap block.
    #[logfn_inputs(TRACE)]
    pub fn is_rooted_by_abstract_heap_block(&self) -> bool {
        match &self.value {
            PathEnum::QualifiedPath { qualifier, .. } => {
                qualifier.is_rooted_by_abstract_heap_block()
            }
            PathEnum::HeapBlock { .. } => true,
            PathEnum::Offset { value } => {
                if let Expression::Offset { left, .. } = &value.expression {
                    if let Expression::Reference(path) | Expression::Variable { path, .. } =
                        &left.expression
                    {
                        return path.is_rooted_by_abstract_heap_block();
                    }
                }
                false
            }
            _ => false,
        }
    }

    /// True if path qualifies an abstract heap block, or another qualified path rooted by an
    /// abstract heap block, where the corresponding memory block has been zeroed by the heap allocator.
    #[logfn_inputs(TRACE)]
    pub fn is_rooted_by_zeroed_heap_block(&self) -> bool {
        match &self.value {
            PathEnum::QualifiedPath { qualifier, .. } => qualifier.is_rooted_by_zeroed_heap_block(),
            PathEnum::HeapBlock { value, .. } => {
                if let Expression::HeapBlock { is_zeroed, .. } = &value.expression {
                    *is_zeroed
                } else {
                    false
                }
            }
            PathEnum::Offset { value } => {
                if let Expression::Offset { left, .. } = &value.expression {
                    if let Expression::Reference(path) | Expression::Variable { path, .. } =
                        &left.expression
                    {
                        return path.is_rooted_by_zeroed_heap_block();
                    }
                }
                false
            }
            _ => false,
        }
    }

    /// True if path qualifies a parameter, or another qualified path rooted by a parameter.
    #[logfn_inputs(TRACE)]
    pub fn is_rooted_by_parameter(&self) -> bool {
        match &self.value {
            PathEnum::QualifiedPath { qualifier, .. } => qualifier.is_rooted_by_parameter(),
            PathEnum::Parameter { .. } => true,
            _ => false,
        }
    }

    // Returns the length of the path.
    #[logfn_inputs(TRACE)]
    pub fn path_length(&self) -> usize {
        match &self.value {
            PathEnum::QualifiedPath { length, .. } => *length,
            _ => 1,
        }
    }

    /// Creates a path that denotes a constant value without a specified memory location.
    #[logfn_inputs(TRACE)]
    pub fn new_constant(value: Rc<AbstractValue>) -> Rc<Path> {
        Rc::new(PathEnum::Constant { value }.into())
    }

    /// Creates a path to the target memory of a reference value.
    #[logfn_inputs(TRACE)]
    pub fn new_deref(address_path: Rc<Path>) -> Rc<Path> {
        let selector = Rc::new(PathSelector::Deref);
        Self::new_qualified(address_path, selector)
    }

    /// Creates a path the selects the discriminant of the enum at the given path.
    #[logfn_inputs(TRACE)]
    pub fn new_discriminant(enum_path: Rc<Path>, environment: &Environment) -> Rc<Path> {
        let selector = Rc::new(PathSelector::Discriminant);
        Self::new_qualified(enum_path, selector).refine_paths(environment)
    }

    /// Creates a path the selects the given field of the struct at the given path.
    #[logfn_inputs(TRACE)]
    pub fn new_field(
        qualifier: Rc<Path>,
        field_index: usize,
        environment: &Environment,
    ) -> Rc<Path> {
        let selector = Rc::new(PathSelector::Field(field_index));
        Self::new_qualified(qualifier, selector).refine_paths(environment)
    }

    /// Creates a path the selects the element at the given index value of the array at the given path.
    #[logfn_inputs(TRACE)]
    pub fn new_index(
        collection_path: Rc<Path>,
        index_value: Rc<AbstractValue>,
        environment: &Environment,
    ) -> Rc<Path> {
        let selector = Rc::new(PathSelector::Index(index_value));
        Self::new_qualified(collection_path, selector).refine_paths(environment)
    }

    /// Creates a path the selects a slice, [0..count_value], from the value at collection_path.
    #[logfn_inputs(TRACE)]
    pub fn new_slice(
        collection_path: Rc<Path>,
        count_value: Rc<AbstractValue>,
        environment: &Environment,
    ) -> Rc<Path> {
        let selector = Rc::new(PathSelector::Slice(count_value));
        Self::new_qualified(collection_path, selector).refine_paths(environment)
    }

    /// Creates a path to the layout of a heap allocated memory block.
    #[logfn_inputs(TRACE)]
    pub fn new_layout(address_path: Rc<Path>) -> Rc<Path> {
        let selector = Rc::new(PathSelector::Layout);
        Self::new_qualified(address_path, selector)
    }

    /// Creates a path to the local variable corresponding to the ordinal.
    #[logfn_inputs(TRACE)]
    pub fn new_local(ordinal: usize) -> Rc<Path> {
        Rc::new(PathEnum::LocalVariable { ordinal }.into())
    }

    /// Creates a path to the local variable corresponding to the ordinal.
    #[logfn_inputs(TRACE)]
    pub fn new_parameter(ordinal: usize) -> Rc<Path> {
        Rc::new(PathEnum::Parameter { ordinal }.into())
    }

    /// Creates a path to the local variable corresponding to the ordinal.
    #[logfn_inputs(TRACE)]
    pub fn new_result() -> Rc<Path> {
        Rc::new(PathEnum::Result.into())
    }

    /// Creates a path to the local variable, parameter or result local, corresponding to the ordinal.
    #[logfn_inputs(TRACE)]
    pub fn new_local_parameter_or_result(ordinal: usize, argument_count: usize) -> Rc<Path> {
        if ordinal == 0 {
            Self::new_result()
        } else if ordinal <= argument_count {
            Self::new_parameter(ordinal)
        } else {
            Self::new_local(ordinal)
        }
    }

    /// Creates a path the selects the length of the array/slice/string at the given path.
    #[logfn_inputs(TRACE)]
    pub fn new_length(array_path: Rc<Path>, environment: &Environment) -> Rc<Path> {
        let selector = Rc::new(PathSelector::Field(1));
        Self::new_qualified(array_path, selector).refine_paths(environment)
    }

    /// Creates a path the selects the given model field of the value at the given path.
    #[logfn_inputs(TRACE)]
    pub fn new_model_field(
        qualifier: Rc<Path>,
        field_name: Rc<String>,
        environment: &Environment,
    ) -> Rc<Path> {
        let selector = Rc::new(PathSelector::ModelField(field_name));
        Self::new_qualified(qualifier, selector).refine_paths(environment)
    }

    /// Creates a path the qualifies the given root path with the given selector.
    #[logfn_inputs(TRACE)]
    pub fn new_qualified(qualifier: Rc<Path>, selector: Rc<PathSelector>) -> Rc<Path> {
        let qualifier_length = qualifier.path_length();
        if qualifier_length >= k_limits::MAX_PATH_LENGTH {
            warn!("max path length exceeded {:?}.{:?}", qualifier, selector);
        }
        assume!(qualifier_length < 1_000_000_000); // We'll run out of memory long before this happens
        Rc::new(
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                length: qualifier_length + 1,
            }
            .into(),
        )
    }

    /// Adds any heap blocks found in embedded index values to the given set.
    #[logfn_inputs(TRACE)]
    pub fn record_heap_blocks(&self, result: &mut HashSet<Rc<AbstractValue>>) {
        match &self.value {
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                (**qualifier).record_heap_blocks(result);
                selector.record_heap_blocks(result);
            }
            PathEnum::HeapBlock { value } => {
                if let Expression::HeapBlock { .. } = &value.expression {
                    result.insert(value.clone());
                } else {
                    verify_unreachable!()
                }
            }
            PathEnum::Offset { value } => {
                if let Expression::Offset { left, right } = &value.expression {
                    left.record_heap_blocks(result);
                    right.record_heap_blocks(result);
                }
            }
            _ => (),
        }
    }
}

pub trait PathRefinement: Sized {
    /// Refine parameters inside embedded index values with the given arguments.
    fn refine_parameters(
        &self,
        arguments: &[(Rc<Path>, Rc<AbstractValue>)],
        fresh: usize,
    ) -> Rc<Path>;

    /// Refine paths that reference other paths.
    /// I.e. when a reference is passed to a function that then returns
    /// or leaks it back to the caller in the qualifier of a path then
    /// we want to dereference the qualifier in order to normalize the path
    /// and not have more than one path for the same location.
    fn refine_paths(&self, environment: &Environment) -> Rc<Path>;

    /// Returns a copy path with the root replaced by new_root.
    fn replace_root(&self, old_root: &Rc<Path>, new_root: Rc<Path>) -> Rc<Path>;
}

impl PathRefinement for Rc<Path> {
    /// Refine parameters inside embedded index values with the given arguments.
    #[logfn_inputs(TRACE)]
    fn refine_parameters(
        &self,
        arguments: &[(Rc<Path>, Rc<AbstractValue>)],
        fresh: usize,
    ) -> Rc<Path> {
        match &self.value {
            PathEnum::LocalVariable { ordinal } => {
                // This is a handy place to put a break point.
                Path::new_local(ordinal + fresh)
            }
            PathEnum::Offset { value } => {
                Rc::new(Path::get_as_path(value.refine_parameters(arguments, fresh)))
            }
            PathEnum::Parameter { ordinal } => arguments[*ordinal - 1].0.clone(),
            PathEnum::Result => Path::new_local(fresh),
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                let refined_qualifier = qualifier.refine_parameters(arguments, fresh);
                let refined_selector = selector.refine_parameters(arguments, fresh);
                Path::new_qualified(refined_qualifier, refined_selector)
            }
            _ => self.clone(),
        }
    }

    /// Refine paths that reference other paths and canonicalize the refinements.
    /// I.e. when a reference is passed to a function that then returns
    /// or leaks it back to the caller in the qualifier of a path then
    /// we want to dereference the qualifier in order to normalize the path
    /// and not have more than one path for the same location.
    #[logfn_inputs(TRACE)]
    fn refine_paths(&self, environment: &Environment) -> Rc<Path> {
        if let Some(mut val) = environment.value_at(&self) {
            // If the environment has self as a key, then self is canonical, since we should only
            // use canonical paths as keys. The value at the canonical key, however, could just
            // be a reference to another path, which is something that happens during refinement.
            if let Expression::Cast { operand, .. } = &val.expression {
                val = operand;
            }
            return match &val.expression {
                Expression::CompileTimeConstant(ConstantDomain::Str(..)) => {
                    Path::new_constant(val.clone())
                }
                Expression::HeapBlock { .. } | Expression::Offset { .. } => {
                    Rc::new(Path::get_as_path(val.refine_paths(environment)))
                }
                Expression::Variable { path, .. } | Expression::Widen { path, .. } => {
                    if let PathEnum::QualifiedPath { selector, .. } = &path.value {
                        if *selector.as_ref() == PathSelector::Deref {
                            // If the path is a deref, it is not just an alias for self, so keep self
                            return self.clone();
                        }
                    }
                    path.clone()
                }
                _ => self.clone(), // self is canonical
            };
        };
        // self is a path that is not a key in the environment. This could be because it is not
        // canonical, which can only be the case if self is a qualified path.
        match &self.value {
            PathEnum::Offset { value } => {
                Rc::new(Path::get_as_path(value.refine_paths(environment)))
            }
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                let refined_selector = selector.refine_paths(environment);
                let refined_qualifier = qualifier.refine_paths(environment);
                // The qualifier is now canonical. But in the context of a selector, we
                // might be able to simplify the qualifier by dropping an explicit dereference
                // or an explicit reference.
                if let PathEnum::QualifiedPath {
                    qualifier: base_qualifier,
                    selector: base_selector,
                    ..
                } = &refined_qualifier.value
                {
                    if *base_selector.as_ref() == PathSelector::Deref {
                        // no need for an explicit deref in a qualifier
                        return Path::new_qualified(base_qualifier.clone(), selector.clone());
                    }
                }
                if let Some(val) = environment.value_at(&refined_qualifier) {
                    match &val.expression {
                        Expression::Variable { path, .. } => {
                            // if path is a deref we just drop it because it becomes implicit
                            if let PathEnum::QualifiedPath {
                                qualifier,
                                selector: var_path_selector,
                                ..
                            } = &path.value
                            {
                                if let PathSelector::Deref = var_path_selector.as_ref() {
                                    // drop the explicit deref
                                    return Path::new_qualified(
                                        qualifier.clone(),
                                        selector.clone(),
                                    );
                                }
                            }
                        }
                        Expression::Reference(path) => {
                            match refined_selector.as_ref() {
                                PathSelector::Deref => {
                                    // We have a *&path sequence. If path is a is heap block, we
                                    // turn self into path[0]. If not, we drop the sequence and return path.
                                    return if matches!(&path.value, PathEnum::HeapBlock {..}) {
                                        Path::new_index(
                                            path.clone(),
                                            Rc::new(0u128.into()),
                                            environment,
                                        )
                                    } else {
                                        path.clone()
                                    };
                                }
                                _ => {
                                    // drop the explicit reference
                                    return Path::new_qualified(path.clone(), selector.clone());
                                }
                            }
                        }
                        _ => (),
                    }
                    if let Expression::Reference(path) = &val.expression {
                        match refined_selector.as_ref() {
                            PathSelector::Deref => {
                                // if selector is a deref we can just drop the &* sequence
                                return path.clone();
                            }
                            _ => {
                                // drop the explicit reference
                                return Path::new_qualified(path.clone(), selector.clone());
                            }
                        }
                    }
                }
                Path::new_qualified(refined_qualifier, refined_selector)
            }
            _ => {
                self.clone() // Non qualified, non offset paths are already canonical
            }
        }
    }

    /// Returns a copy path with the root replaced by new_root.
    #[logfn_inputs(TRACE)]
    fn replace_root(&self, old_root: &Rc<Path>, new_root: Rc<Path>) -> Rc<Path> {
        match &self.value {
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                let new_qualifier = if *qualifier == *old_root {
                    new_root
                } else {
                    qualifier.replace_root(old_root, new_root)
                };
                Path::new_qualified(new_qualifier, selector.clone())
            }
            _ => new_root,
        }
    }
}

/// The selector denotes a de-referenced item, field, or element, or slice.
#[derive(Serialize, Deserialize, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum PathSelector {
    /// The layout specified to the allocate/deallocate call.
    Layout,

    /// Given a path that denotes a reference, select the thing the reference points to.
    Deref,

    /// The tag used to indicate which case of an enum is used for a particular enum value.
    Discriminant,

    /// Select the struct field with the given index.
    Field(usize),

    /// Select the collection element with the index specified by the abstract value.
    Index(Rc<AbstractValue>),

    /// Selects slice[0..value] where slice is the qualifier and value the selector parameter.
    Slice(Rc<AbstractValue>),

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
    /// If `from_end` is true `slice[from..slice.len() - to]`.
    /// Otherwise `array[from..to]`.
    ConstantSlice { from: u32, to: u32, from_end: bool },

    /// "Downcast" to a variant of an ADT. Currently, MIR only introduces
    /// this for ADTs with more than one variant. The value is the ordinal of the variant.
    Downcast(Rc<String>, usize),

    /// Select the struct model field with the given name.
    /// A model field is a specification construct used during MIRAI verification
    /// and does not have a runtime location.
    ModelField(Rc<String>),
}

impl Debug for PathSelector {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            PathSelector::Layout => f.write_str("layout"),
            PathSelector::Deref => f.write_str("deref"),
            PathSelector::Discriminant => f.write_str("discr"),
            PathSelector::Field(index) => index.fmt(f),
            PathSelector::Index(value) => f.write_fmt(format_args!("[{:?}]", value)),
            PathSelector::Slice(value) => f.write_fmt(format_args!("[0..{:?}]", value)),
            PathSelector::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => f.write_fmt(format_args!(
                "[offset: {}, min_length: {}, from_end: {}",
                offset, min_length, from_end
            )),
            PathSelector::ConstantSlice { from, to, from_end } => {
                f.write_fmt(format_args!("[{} : {}, from_end: {}]", from, to, from_end))
            }
            PathSelector::Downcast(name, index) => {
                f.write_fmt(format_args!("as {}({})", name, *index))
            }
            PathSelector::ModelField(name) => name.fmt(f),
        }
    }
}

impl PathSelector {
    /// Adds any abstract heap addresses found in embedded index values to the given set.
    #[logfn_inputs(TRACE)]
    pub fn record_heap_blocks(&self, result: &mut HashSet<Rc<AbstractValue>>) {
        match self {
            PathSelector::Index(value) | PathSelector::Slice(value) => {
                value.record_heap_blocks(result);
            }
            _ => (),
        }
    }
}

pub trait PathSelectorRefinement: Sized {
    /// Refine parameters inside embedded index values with the given arguments.
    fn refine_parameters(&self, arguments: &[(Rc<Path>, Rc<AbstractValue>)], fresh: usize) -> Self;

    /// Returns a value that is simplified (refined) by replacing values with Variable(path) expressions
    /// with the value at that path (if there is one). If no refinement is possible
    /// the result is simply a clone of this value. This refinement only makes sense
    /// following a call to refine_parameters.
    fn refine_paths(&self, environment: &Environment) -> Self;
}

impl PathSelectorRefinement for Rc<PathSelector> {
    /// Refine parameters inside embedded index values with the given arguments.
    #[logfn_inputs(TRACE)]
    fn refine_parameters(
        &self,
        arguments: &[(Rc<Path>, Rc<AbstractValue>)],
        fresh: usize,
    ) -> Rc<PathSelector> {
        match self.as_ref() {
            PathSelector::Index(value) => {
                let refined_value = value.refine_parameters(arguments, fresh);
                Rc::new(PathSelector::Index(refined_value))
            }
            PathSelector::Slice(value) => {
                let refined_value = value.refine_parameters(arguments, fresh);
                Rc::new(PathSelector::Slice(refined_value))
            }
            _ => self.clone(),
        }
    }

    /// Returns a value that is simplified (refined) by replacing values with Variable(path) expressions
    /// with the value at that path (if there is one). If no refinement is possible
    /// the result is simply a clone of this value. This refinement only makes sense
    /// following a call to refine_parameters.
    #[logfn_inputs(TRACE)]
    fn refine_paths(&self, environment: &Environment) -> Rc<PathSelector> {
        match self.as_ref() {
            PathSelector::Index(value) => {
                let refined_value = value.refine_paths(environment);
                Rc::new(PathSelector::Index(refined_value))
            }
            PathSelector::Slice(value) => {
                let refined_value = value.refine_paths(environment);
                Rc::new(PathSelector::Slice(refined_value))
            }
            _ => self.clone(),
        }
    }
}
