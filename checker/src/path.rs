// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//
use std::collections::hash_map::DefaultHasher;
use std::collections::HashSet;
use std::fmt::{Debug, Formatter, Result};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use log_derive::*;
use serde::{Deserialize, Serialize};

use mirai_annotations::*;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Ty, TyCtxt};

use crate::abstract_value::{self, AbstractValue, AbstractValueTrait};
use crate::constant_domain::ConstantDomain;
use crate::environment::Environment;
use crate::expression::{Expression, ExpressionType};
use crate::tag_domain::Tag;
use crate::{k_limits, utils};

/// During join and widen operations, paths are copied from one environment to another, causing them
/// to get rehashed. This turns out to be expensive, so for this case we cache the hash to avoid
/// recomputing it. The caching has a cost, so only use this in cases where it is highly likely
/// that the path will be hashed more than once.
#[derive(Serialize, Deserialize, Clone, Eq, Ord, PartialOrd)]
pub struct Path {
    pub value: PathEnum,
    hash: u64,
}

#[derive(Debug, Clone)]
pub enum PathOrFunction<'tcx> {
    Path(Rc<Path>, bool),
    Function(Ty<'tcx>, Rc<AbstractValue>),
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

    /// If the abstract value is the contents of a memory location identified by
    /// a path, then return that path. If not, returns a path that is computed.
    #[logfn_inputs(TRACE)]
    pub fn get_as_path(value: Rc<AbstractValue>) -> Rc<Path> {
        Rc::new(match &value.expression {
            Expression::Cast { operand, .. } => {
                return Path::get_as_path(operand.clone());
            }
            Expression::HeapBlock { .. } => {
                return Path::new_heap_block(value);
            }
            Expression::Offset { .. } => PathEnum::Offset { value }.into(),
            Expression::UninterpretedCall { path, .. }
            | Expression::InitialParameterValue { path, .. }
            | Expression::Variable { path, .. } => path.as_ref().clone(),
            _ => PathEnum::Computed { value }.into(),
        })
    }

    /// When splitting paths while doing weak updates, it is important to not refine paths because
    /// they are already canonical and because doing so can lead to recursive loops as refined paths
    /// re-introduce joined paths that have been split earlier.
    /// A split path, however, can serve as the qualifier of a newly constructed qualified path
    /// and the qualified path might not be canonical. This routine tries to remove the two sources of
    /// de-canonicalization that are currently know. Essentially: when a path that binds to a value
    /// that is a reference is explicitly dereferenced by the selector, the canonical path will
    /// be the one without the ref-deref, or the actual heap block, if the path binds to a heap
    /// location. This routine returns a re-canonicalized path in the two scenarios above,
    /// otherwise returns `None`.
    ///
    /// If the function returns a re-canonicalized path, which is used as the qualifier of a newly
    /// constructed qualified path, the caller of this function should check if the selector of the
    /// qualified path is `PathSelector::Deref`. If so, the deref selector should also be removed.
    #[logfn_inputs(TRACE)]
    pub fn try_to_dereference(path: &Rc<Path>, environment: &Environment) -> Option<Rc<Path>> {
        if let PathEnum::Computed { value } = &path.value {
            if let Expression::Reference(path) = &value.expression {
                return Some(path.clone());
            }
        } else if let Some(value) = environment.value_map.get(path) {
            if let Expression::Reference(path) = &value.expression {
                return Some(path.clone());
            }
        }
        None
    }
}

/// A path represents a left hand side expression.
/// When the actual expression is evaluated at runtime it will resolve to a particular memory
/// location. During analysis it is used to keep track of state changes.
#[derive(Serialize, Deserialize, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum PathEnum {
    /// A path that provides a location for a value that is not associated with a place in MIR.
    /// This can be a structured constant or it can be a computed value. A computed value can
    /// be a reference, hence a computed path may be an alias for one or more other paths and
    /// any updates to a computed path should taking aliasing into account, by doing weak updates.
    Computed { value: Rc<AbstractValue> },

    /// A dynamically allocated memory block. Unlike a Computed path, the value of a HeapBlock
    /// path must have an expression of kind Expression::HeapBlock. Conversely, a heap block
    /// value will never be wrapped by a Computed path.
    HeapBlock { value: Rc<AbstractValue> },

    /// locals [arg_count+1..] are the local variables and compiler temporaries.
    LocalVariable {
        ordinal: usize,
        #[serde(skip)]
        type_index: usize,
    },

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
        summary_cache_key: Rc<str>,
        /// The type to use when the static variable value is not yet available.
        expression_type: ExpressionType,
    },

    /// This path points to data that is not used, but exists only to satisfy a static checker
    /// that a generic parameter is actually used.
    PhantomData,

    /// The ordinal is an index into a method level table of MIR bodies.
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
            PathEnum::Computed { value } => value.fmt(f),
            PathEnum::HeapBlock { value } => f.write_fmt(format_args!("<{:?}>", value)),
            PathEnum::LocalVariable {
                ordinal,
                type_index,
            } => f.write_fmt(format_args!("local_{}({})", ordinal, type_index)),
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

pub trait PathRoot: Sized {
    fn contains_deref(&self) -> bool;
    fn get_path_root(&self) -> &Self;
    fn get_parameter_root_ordinal(&self) -> Option<usize>;
    fn has_tagged_subcomponent(&self, tag: &Tag, env: &Environment) -> bool;
    fn is_rooted_by(&self, root: &Rc<Path>) -> bool;
    fn is_rooted_by_non_local_structure(&self) -> bool;
    fn is_rooted_by_zeroed_heap_block(&self) -> bool;
    fn is_rooted_by_parameter(&self) -> bool;
}

impl PathRoot for Rc<Path> {
    /// True if any part of the path is a deref. Used to distinguish paths
    /// that are part of contiguous structures from paths that deference pointers.
    /// The former have to move when the overall structure moves.
    #[logfn_inputs(TRACE)]
    fn contains_deref(&self) -> bool {
        if let PathEnum::QualifiedPath {
            qualifier,
            selector,
            ..
        } = &self.value
        {
            if matches!(selector.as_ref(), PathSelector::Deref) {
                true
            } else {
                qualifier.contains_deref()
            }
        } else {
            false
        }
    }

    /// Returns a reference to the effective root of the given path.
    #[logfn_inputs(TRACE)]
    fn get_path_root(&self) -> &Rc<Path> {
        match &self.value {
            PathEnum::Computed { value } | PathEnum::Offset { value } => value.get_path_root(self),
            PathEnum::QualifiedPath { qualifier, .. } => qualifier.get_path_root(),
            _ => self,
        }
    }

    /// Returns the ordinal of the parameter at the root of this path, if there is one.
    #[logfn_inputs(TRACE)]
    fn get_parameter_root_ordinal(&self) -> Option<usize> {
        if let PathEnum::Parameter { ordinal } = self.get_path_root().value {
            Some(ordinal)
        } else {
            None
        }
    }

    /// Returns true if the given expression is known to have a subcomponent in the given
    /// environment that is tagged with the given tag. False does not imply the absence of the tag.
    #[logfn_inputs(TRACE)]
    fn has_tagged_subcomponent(&self, tag: &Tag, env: &Environment) -> bool {
        let root = self.get_path_root();
        for (p, v) in env.value_map.iter() {
            if p != root && !p.is_rooted_by(root) {
                continue;
            }
            if v.has_tag(tag).as_bool_if_known().unwrap_or(false)
                || v.expression.has_tagged_subcomponent(tag, env)
            {
                return true;
            }
        }
        false
    }

    /// True if path qualifies root, or another qualified path rooted by root.
    #[logfn_inputs(TRACE)]
    fn is_rooted_by(&self, root: &Rc<Path>) -> bool {
        match &self.value {
            PathEnum::Computed { value } => {
                if let Expression::InitialParameterValue { path, .. }
                | Expression::Reference(path)
                | Expression::Variable { path, .. } = &value.expression
                {
                    return *path == *root || path.is_rooted_by(root);
                }
                false
            }
            PathEnum::Offset { value } => {
                if let Expression::Offset { left, .. } = &value.expression {
                    if let Expression::InitialParameterValue { path, .. }
                    | Expression::Reference(path)
                    | Expression::Variable { path, .. } = &left.expression
                    {
                        return *path == *root || path.is_rooted_by(root);
                    }
                }
                false
            }
            PathEnum::QualifiedPath { qualifier, .. } => {
                *qualifier == *root || qualifier.is_rooted_by(root)
            }
            _ => false,
        }
    }

    /// True if path qualifies an abstract heap block, string or static, or another qualified path
    /// rooted by an abstract heap block, string or static.
    #[logfn_inputs(TRACE)]
    fn is_rooted_by_non_local_structure(&self) -> bool {
        match &self.get_path_root().value {
            PathEnum::HeapBlock { .. } | PathEnum::StaticVariable { .. } => true,
            PathEnum::Computed { value } => {
                matches!(
                    value.expression,
                    Expression::CompileTimeConstant(ConstantDomain::Str(..))
                )
            }
            _ => false,
        }
    }

    /// True if path qualifies an abstract heap block, or another qualified path rooted by an
    /// abstract heap block, where the corresponding memory block has been zeroed by the heap allocator.
    #[logfn_inputs(TRACE)]
    fn is_rooted_by_zeroed_heap_block(&self) -> bool {
        if let PathEnum::HeapBlock { value, .. } = &self.get_path_root().value {
            if let Expression::HeapBlock { is_zeroed, .. } = &value.expression {
                return *is_zeroed;
            }
        }
        false
    }

    /// True if path qualifies a parameter, or another qualified path rooted by a parameter.
    #[logfn_inputs(TRACE)]
    fn is_rooted_by_parameter(&self) -> bool {
        matches!(self.get_path_root().value, PathEnum::Parameter { .. })
    }
}

impl Path {
    /// Returns true if the path contains a value whose expression contains a local variable.
    #[logfn_inputs(TRACE)]
    pub fn contains_local_variable(&self, is_post_condition: bool) -> bool {
        match &self.value {
            PathEnum::Computed { value } => {
                value.expression.contains_local_variable(is_post_condition)
            }
            PathEnum::HeapBlock { .. } => true,
            PathEnum::LocalVariable { .. } => true,
            PathEnum::Offset { value } => {
                value.expression.contains_local_variable(is_post_condition)
            }
            PathEnum::Parameter { .. } => false,
            // In a post condition, a function result does not count as a local variable of the function
            PathEnum::Result => !is_post_condition,
            // A caller will not know anything about a static variable that is not known locally
            PathEnum::StaticVariable { .. } => true,
            PathEnum::PhantomData => false,
            PathEnum::PromotedConstant { .. } => true,
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                qualifier.contains_local_variable(is_post_condition) || {
                    if let PathSelector::Index(value) = selector.as_ref() {
                        value.expression.contains_local_variable(is_post_condition)
                    } else {
                        false
                    }
                }
            }
        }
    }

    /// Returns true if the path contains a value whose expression is TOP.
    #[logfn_inputs(TRACE)]
    pub fn contains_top(&self) -> bool {
        match &self.value {
            PathEnum::Computed { value } => value.expression.contains_top(),
            PathEnum::HeapBlock { .. } => false,
            PathEnum::LocalVariable { .. } => true,
            PathEnum::Offset { value } => value.expression.contains_top(),
            PathEnum::Parameter { .. } => false,
            PathEnum::Result => false,
            PathEnum::StaticVariable { .. } => true,
            PathEnum::PhantomData => false,
            PathEnum::PromotedConstant { .. } => false,
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                qualifier.contains_top() || {
                    if let PathSelector::Index(value) = selector.as_ref() {
                        value.expression.contains_top()
                    } else {
                        false
                    }
                }
            }
        }
    }

    /// Returns an abstract value for "true if the path is the same runtime location as other"
    #[logfn_inputs(TRACE)]
    pub fn equals(&self, other: &Rc<Path>) -> Rc<AbstractValue> {
        if self.eq(other.as_ref()) {
            return Rc::new(abstract_value::TRUE);
        }
        return match (&self.value, &other.value) {
            (PathEnum::Computed { value: v1 }, PathEnum::Computed { value: v2 })
            | (PathEnum::HeapBlock { value: v1 }, PathEnum::HeapBlock { value: v2 }) => {
                v1.equals(v2.clone())
            }
            (PathEnum::HeapBlock { value: v1 }, PathEnum::Offset { value: v2 })
            | (PathEnum::Offset { value: v2 }, PathEnum::HeapBlock { value: v1 }) => {
                if let Expression::Offset {
                    left: l2,
                    right: r2,
                } = &v2.expression
                {
                    if let Expression::Reference(p2) = &l2.expression {
                        if let PathEnum::HeapBlock { value: v2 } = &p2.value {
                            v1.equals(v2.clone()).and(r2.equals(Rc::new(0_i128.into())))
                        } else {
                            Rc::new(abstract_value::FALSE)
                        }
                    } else {
                        Rc::new(abstract_value::FALSE)
                    }
                } else {
                    unreachable!("path offset must wrap expression offset");
                }
            }
            (PathEnum::Offset { value: v1 }, PathEnum::Offset { value: v2 }) => {
                if let (
                    Expression::Offset {
                        left: l1,
                        right: r1,
                    },
                    Expression::Offset {
                        left: l2,
                        right: r2,
                    },
                ) = (&v1.expression, &v2.expression)
                {
                    l1.equals(l2.clone()).and(r1.equals(r2.clone()))
                } else {
                    unreachable!("path offset must wrap expression offset");
                }
            }
            (
                PathEnum::QualifiedPath {
                    qualifier: q1,
                    selector: s1,
                    ..
                },
                PathEnum::QualifiedPath {
                    qualifier: q2,
                    selector: s2,
                    ..
                },
            ) => s1.equals(s2).and(q1.equals(q2)),
            _ => Rc::new(abstract_value::FALSE),
        };
    }

    /// Returns the index value of the index path qualified by qualifier.
    #[logfn_inputs(TRACE)]
    pub fn get_index_value_qualified_by(&self, root: &Rc<Path>) -> Option<Rc<AbstractValue>> {
        match &self.value {
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                if let PathSelector::Index(value) = selector.as_ref() {
                    if *qualifier == *root {
                        Some(value.clone())
                    } else {
                        qualifier.get_index_value_qualified_by(root)
                    }
                } else {
                    qualifier.get_index_value_qualified_by(root)
                }
            }
            _ => None,
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

    /// Creates a path to a value. A common use for such a path is a qualifier
    /// for a tag, a deref or a model field. It can also be a source path of a copy operation
    /// where the target path is the location of a non structured value. And so on.
    /// NB: A computed path may be an alias for other paths, so remember to do weak updates
    /// when using a computed path as key in the environment. When reading, remember to abstract
    /// over the values from all paths that may alias this path.
    #[logfn_inputs(TRACE)]
    pub fn new_computed(value: Rc<AbstractValue>) -> Rc<Path> {
        Rc::new(PathEnum::Computed { value }.into())
    }

    /// Creates a path to the target memory of a reference value.
    #[logfn_inputs(TRACE)]
    pub fn new_deref(address_path: Rc<Path>, target_type: ExpressionType) -> Rc<Path> {
        if let PathEnum::Computed { value } = &address_path.value {
            let deref_value = value.dereference(target_type);
            return Path::get_as_path(deref_value);
        }
        let selector = Rc::new(PathSelector::Deref);
        Self::new_qualified(address_path, selector)
    }

    /// Creates a path the selects the discriminant of the enum at the given path.
    #[logfn_inputs(TRACE)]
    pub fn new_discriminant(enum_path: Rc<Path>) -> Rc<Path> {
        let selector = Rc::new(PathSelector::Discriminant);
        Self::new_qualified(enum_path, selector)
    }

    /// Creates a path the selects the function of the function/closure value at the given path.
    #[logfn_inputs(TRACE)]
    pub fn new_function(func_path: Rc<Path>) -> Rc<Path> {
        if let PathEnum::QualifiedPath { selector, .. } = &func_path.value {
            if matches!(selector.as_ref(), PathSelector::Function) {
                return func_path;
            }
        }
        let selector = Rc::new(PathSelector::Function);
        Self::new_qualified(func_path, selector)
    }

    /// Creates a path the selects the given field of the struct at the given path.
    #[logfn_inputs(TRACE)]
    pub fn new_field(qualifier: Rc<Path>, field_index: usize) -> Rc<Path> {
        let selector = Rc::new(PathSelector::Field(field_index));
        Self::new_qualified(qualifier, selector)
    }

    /// Creates a path the selects the given field of the union at the given path.
    #[logfn_inputs(TRACE)]
    pub fn new_union_field(qualifier: Rc<Path>, case_index: usize, num_cases: usize) -> Rc<Path> {
        let selector = Rc::new(PathSelector::UnionField {
            case_index,
            num_cases,
        });
        Self::new_qualified(qualifier, selector)
    }

    /// Creates a path to the given heap block.
    #[logfn_inputs(TRACE)]
    pub fn new_heap_block(value: Rc<AbstractValue>) -> Rc<Path> {
        precondition!(matches!(&value.expression, Expression::HeapBlock { .. }));
        Rc::new(PathEnum::HeapBlock { value }.into())
    }

    /// Creates a path the selects the element at the given index value of the array at the given path.
    #[logfn_inputs(TRACE)]
    pub fn new_index(collection_path: Rc<Path>, index_value: Rc<AbstractValue>) -> Rc<Path> {
        let selector = Rc::new(PathSelector::Index(index_value));
        Self::new_qualified(collection_path, selector)
    }

    /// Creates a path the selects a slice, [0..count_value], from the value at collection_path.
    #[logfn_inputs(TRACE)]
    pub fn new_slice(collection_path: Rc<Path>, count_value: Rc<AbstractValue>) -> Rc<Path> {
        let selector = Rc::new(PathSelector::Slice(count_value));
        Self::new_qualified(collection_path, selector)
    }

    /// Creates a path to the static defined by def_id.
    pub fn new_static(tcx: TyCtxt<'_>, def_id: DefId) -> Rc<Path> {
        let ty = tcx.type_of(def_id);
        let name = utils::summary_key_str(tcx, def_id);
        Rc::new(
            PathEnum::StaticVariable {
                def_id: Some(def_id),
                summary_cache_key: name,
                expression_type: ExpressionType::from(ty.kind()),
            }
            .into(),
        )
    }

    /// Creates a path to the layout of a heap allocated memory block.
    #[logfn_inputs(TRACE)]
    pub fn new_layout(address_path: Rc<Path>) -> Rc<Path> {
        let selector = Rc::new(PathSelector::Layout);
        Self::new_qualified(address_path, selector)
    }

    /// Creates a path to the local variable corresponding to the ordinal.
    #[logfn_inputs(TRACE)]
    pub fn new_local(ordinal: usize, type_index: usize) -> Rc<Path> {
        Rc::new(
            PathEnum::LocalVariable {
                ordinal,
                type_index,
            }
            .into(),
        )
    }

    /// Creates a path to the parameter corresponding to the ordinal.
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
    pub fn new_local_parameter_or_result(
        ordinal: usize,
        argument_count: usize,
        type_index: usize,
    ) -> Rc<Path> {
        if ordinal == 0 {
            Self::new_result()
        } else if ordinal <= argument_count {
            Self::new_parameter(ordinal)
        } else {
            Self::new_local(ordinal, type_index)
        }
    }

    /// Creates a path the selects the length of the array/slice/string at the given path.
    #[logfn_inputs(TRACE)]
    pub fn new_length(array_path: Rc<Path>) -> Rc<Path> {
        let selector = Rc::new(PathSelector::Field(1));
        Self::new_qualified(array_path, selector)
    }

    /// Creates a path the selects the given model field of the value at the given path.
    #[logfn_inputs(TRACE)]
    pub fn new_model_field(qualifier: Rc<Path>, field_name: Rc<str>) -> Rc<Path> {
        let selector = Rc::new(PathSelector::ModelField(field_name));
        Self::new_qualified(qualifier, selector)
    }

    /// Creates a path that selects the tag field of the (non-scalar) value of the given path.
    #[logfn_inputs(TRACE)]
    pub fn new_tag_field(qualifier: Rc<Path>) -> Rc<Path> {
        let selector = Rc::new(PathSelector::TagField);
        Self::new_qualified(qualifier, selector)
    }

    /// Creates a path the qualifies the given root path with the given selector.
    #[logfn_inputs(TRACE)]
    pub fn new_qualified(qualifier: Rc<Path>, selector: Rc<PathSelector>) -> Rc<Path> {
        if let PathEnum::Computed { value } = &qualifier.value {
            // A path to bottom must stay that way even if qualified by a selector.
            if value.is_bottom() {
                return qualifier;
            }
        }
        let qualifier_length = qualifier.path_length();
        if qualifier_length >= k_limits::MAX_PATH_LENGTH {
            return Path::new_computed(abstract_value::BOTTOM.into());
        }
        Rc::new(
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                length: qualifier_length + 1,
            }
            .into(),
        )
    }

    /// Adds any heap blocks and string values found in embedded values to the given set.
    #[logfn_inputs(TRACE)]
    pub fn record_heap_blocks_and_strings(&self, result: &mut HashSet<Rc<AbstractValue>>) {
        match &self.value {
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                (**qualifier).record_heap_blocks_and_strings(result);
                selector.record_heap_blocks_and_strings(result);
            }
            PathEnum::HeapBlock { value } => {
                if let Expression::HeapBlock { .. } = &value.expression {
                    result.insert(value.clone());
                } else {
                    unreachable!(); // Heap blocks paths should have HeapBlock values.
                }
            }
            PathEnum::Offset { value } => {
                if let Expression::Offset { left, right } = &value.expression {
                    left.record_heap_blocks_and_strings(result);
                    right.record_heap_blocks_and_strings(result);
                }
            }
            PathEnum::Computed { value }
                if matches!(
                    value.expression,
                    Expression::CompileTimeConstant(ConstantDomain::Str(..))
                ) =>
            {
                result.insert(value.clone());
            }
            PathEnum::StaticVariable {
                expression_type, ..
            } => {
                result.insert(AbstractValue::make_typed_unknown(
                    *expression_type,
                    Rc::new(self.clone()),
                ));
            }
            _ => (),
        }
    }
}

pub trait PathRefinement: Sized {
    /// Refine parameters inside embedded expressions with the given arguments and canonicalizes result.
    fn refine_parameters_and_paths(
        &self,
        args: &[(Rc<Path>, Rc<AbstractValue>)],
        result: &Option<Rc<Path>>,
        pre_env: &Environment,
        post_env: &Environment,
        fresh: usize,
    ) -> Rc<Path>;

    /// Reduces a path to its canonical form. For example, *&p and p are equivalent if p is not
    /// structured, and this will lead to inaccuracies if *&p and p are not always bound to the
    /// same value in an environment. To avoid this, we always reduce a path to the it shortest
    /// form, after removing indirections. This does not solve the alias problem entirely, but
    /// it reduces the problem to dealing with PathEnum::Computed and PathSelector::Index and
    /// PathSelector::Slice.
    fn canonicalize(&self, environment: &Environment) -> Rc<Path>;

    /// Returns a copy of self with the root replaced by new_root.
    fn replace_root(&self, old_root: &Rc<Path>, new_root: Rc<Path>) -> Rc<Path>;

    /// Replaces a path prefix that is an initial parameter value, with just a reference to
    /// the parameter value. This only makes sense when the resulting path will be be embedded
    /// in wrapper itself. I.e. a canonical path only ever contains one wrapper.
    fn remove_initial_value_wrapper(&self) -> Rc<Path>;

    /// Returns a copy of self with the selector replace by a new selector.
    /// It is only legal to call this on a qualified path.
    fn add_or_replace_selector(&self, new_selector: Rc<PathSelector>) -> Rc<Path>;

    /// Returns a copy of self with its last selector removed if that matches the given selector.
    fn remove_selector(&self, selector: Rc<PathSelector>) -> Rc<Path>;
}

impl PathRefinement for Rc<Path> {
    /// Refine parameters inside embedded expressions with the given arguments.
    #[logfn_inputs(TRACE)]
    fn refine_parameters_and_paths(
        &self,
        args: &[(Rc<Path>, Rc<AbstractValue>)],
        result: &Option<Rc<Path>>,
        pre_env: &Environment,
        post_env: &Environment,
        fresh: usize,
    ) -> Rc<Path> {
        match &self.value {
            PathEnum::Computed { value } => Path::get_as_path(
                value.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
            ),
            PathEnum::HeapBlock { value } => {
                let refined_value =
                    value.refine_parameters_and_paths(args, result, pre_env, post_env, fresh);
                Path::new_heap_block(refined_value)
            }
            PathEnum::LocalVariable {
                ordinal,
                type_index,
            } => {
                if (*ordinal) != 999_999 {
                    // This is a handy place to put a break point.
                    let _x = *ordinal;
                }
                Path::new_local((*ordinal) + fresh, *type_index)
            }
            PathEnum::Offset { value } => Path::get_as_path(
                value.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
            ),
            PathEnum::Parameter { ordinal } => {
                if *ordinal > args.len() {
                    warn!("Summary refers to a parameter that does not have a matching argument");
                    Path::new_computed(Rc::new(abstract_value::BOTTOM))
                } else {
                    args[*ordinal - 1].0.clone()
                }
            }
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                let refined_selector =
                    selector.refine_parameters_and_paths(args, result, pre_env, post_env, fresh);
                let refined_qualifier =
                    qualifier.refine_parameters_and_paths(args, result, pre_env, post_env, fresh);
                if refined_qualifier == *qualifier && refined_selector == *selector {
                    self.clone()
                } else {
                    Path::new_qualified(refined_qualifier, refined_selector).canonicalize(post_env)
                }
            }
            PathEnum::Result => {
                if result.is_none() {
                    unreachable!(
                        "A summary that references its result should have a path for the result"
                    );
                } else {
                    result.as_ref().unwrap().clone()
                }
            }
            PathEnum::StaticVariable { .. }
            | PathEnum::PhantomData
            | PathEnum::PromotedConstant { .. } => self.clone(),
        }
    }

    /// Reduces a path to its canonical form. For example, *&p and p are equivalent if p is not
    /// structured, and this will lead to inaccuracies if *&p and p are not always bound to the
    /// same value in an environment. To avoid this, we always reduce a path to the it shortest
    /// form, after removing indirections. This does not solve the alias problem entirely, but
    /// it reduces the problem to dealing with PathEnum::Computed and PathSelector::Index and
    /// PathSelector::Slice.
    #[logfn_inputs(TRACE)]
    fn canonicalize(&self, environment: &Environment) -> Rc<Path> {
        if let Some(val) = environment.value_at(self) {
            // If self binds to value &p then self and path &p are equivalent paths.
            // Since many paths can bind to &p and p is canonical (by construction of &p).
            // we replace self with &p.

            // This reasoning is extended to any expression that has type ExpressionType::ThinPointer.
            // With one exception: we guard against the case where self may bind to old(self).
            // This can happen when self is rooted in a parameter and has been accessed before
            // being assigned to. After any assignment, self and old(self) are not aliases so
            // they need to stay distinct, not least because otherwise the first assignment
            // to self will actually update old(self).
            let mut not_dummy = true;
            if let Expression::InitialParameterValue { path, .. } = &val.expression {
                if self.eq(path) {
                    not_dummy = false;
                }
            }
            // If self binds to value &p then self and path &p are equivalent paths.
            // Since self is derived from p, we use path &p as the canonical form.
            // If we used self instead, then what would we do if we encounter another
            // path that also binds to value &p?
            if not_dummy && val.expression.infer_type() == ExpressionType::ThinPointer {
                if matches!(&val.expression, Expression::Offset { .. }) {
                    return Path::get_as_path(val.clone());
                }
                return Path::new_computed(val.clone());
            }
            // If the environment contains a value for (key) self, self must be canonical.
            // At any rate, it makes no sense to turn it into another path that likely
            // does not lead to the known value.
            return self.clone();
        }

        // If self is a qualified path, then recursive canonicalization of the qualifier may
        // cause substitutions (as above) and that could result in a non canonical qualified path
        // if *p becomes *&q. We thus need some additional logic to canonicalize the overall
        // path once the qualifier has been canonicalized.
        if let PathEnum::QualifiedPath {
            qualifier,
            selector,
            ..
        } = &self.value
        {
            let canonical_qualifier = qualifier.canonicalize(environment);
            // If the canonical qualifier binds to a special value, we may need to deconstruct that
            // value before constructing the qualified path.
            let qualifier_as_value = if let PathEnum::Computed { value }
            | PathEnum::Offset { value } = &canonical_qualifier.value
            {
                Some(value)
            } else {
                environment.value_at(&canonical_qualifier)
            };

            if let Some(value) = qualifier_as_value {
                match &value.expression {
                    Expression::InitialParameterValue { path, .. } => {
                        let ps = Path::new_qualified(path.clone(), selector.clone());
                        return if let Some(v) = environment.value_at(&ps) {
                            if let Expression::InitialParameterValue { path: p, .. } = &v.expression
                            {
                                if ps.eq(p) {
                                    // The p.s is the key for old(p.s), so ps by itself is unambiguous.
                                    return ps;
                                }
                            }
                            if matches!(path.value, PathEnum::Parameter { .. }) {
                                // old(p).s => p.s if there has been no assignment to p, which is
                                // the case because qualifier_as_value is a dummy value.
                                Path::new_qualified(path.clone(), selector.clone())
                            } else {
                                Path::new_qualified(
                                    Path::new_computed(value.clone()),
                                    selector.clone(),
                                )
                            }
                        } else {
                            // Since there is no entry for ps in the environment, looking up
                            // its value will create it (in a context where the type of p.s
                            // is known).
                            ps
                        };
                    }
                    Expression::Offset { left, right } if right.is_zero() => {
                        if let Expression::Reference(p) = &left.expression {
                            // *offset(&p, 0) becomes p
                            if **selector == PathSelector::Deref {
                                return p.clone();
                            }
                        }
                        // offset(p, 0) becomes p in a qualifier
                        let p = Path::get_as_path(value.clone());
                        return Path::new_qualified(p, selector.clone());
                    }
                    // *&p is equivalent to p and (&p).q is equivalent to p.q, etc.
                    Expression::Reference(p) => {
                        // *&p just becomes p
                        // (except when the value at p is structured and the result is assigned to a local,
                        // but such paths are never canonicalized).
                        if **selector == PathSelector::Deref {
                            return p.clone();
                        }
                        // since self is a qualified path we have to drop the reference operator
                        // since selectors implicitly dereference pointers.
                        return Path::new_qualified(p.clone(), selector.clone());
                    }
                    Expression::Variable { path, .. } => {
                        return Path::new_qualified(path.clone(), selector.clone());
                    }
                    _ => {
                        if **selector == PathSelector::Deref {
                            return Path::new_qualified(
                                Path::get_as_path(value.clone()),
                                selector.clone(),
                            );
                        }
                    }
                }
            }
            // An impossible downcast is equivalent to BOTTOM
            if let PathSelector::Downcast(_, variant) = selector.as_ref() {
                let discriminator = Path::new_discriminant(canonical_qualifier.clone());
                if let Some(val) = environment.value_at(&discriminator) {
                    if let Expression::CompileTimeConstant(ConstantDomain::U128(ordinal)) =
                        &val.expression
                    {
                        if (*variant as u128) != *ordinal {
                            // The downcast is impossible in this calling context
                            return Path::new_computed(Rc::new(abstract_value::BOTTOM));
                        }
                    }
                }
            }
            if let PathSelector::Slice(count) = selector.as_ref() {
                if let Expression::CompileTimeConstant(ConstantDomain::U128(count)) =
                    &count.expression
                {
                    if let PathEnum::QualifiedPath {
                        qualifier,
                        selector,
                        ..
                    } = &qualifier.value
                    {
                        if **selector == PathSelector::Deref {
                            if let PathEnum::Offset { value } = &qualifier.value {
                                if let Expression::Offset { left, right } = &value.expression {
                                    if let Expression::CompileTimeConstant(ConstantDomain::I128(
                                        from,
                                    )) = &right.expression
                                    {
                                        let base_path = Path::new_deref(
                                            Path::get_as_path(left.clone()),
                                            ExpressionType::NonPrimitive,
                                        );
                                        let to = *from + (*count as i128);
                                        let selector = Rc::new(PathSelector::ConstantSlice {
                                            from: *from as u64,
                                            to: to as u64,
                                            from_end: false,
                                        });
                                        return Path::new_qualified(base_path, selector);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            Path::new_qualified(canonical_qualifier, selector.clone())
        } else {
            self.clone()
        }
    }

    /// Replaces a path prefix that is an initial parameter value, with just a reference to
    /// the parameter value. This only makes sense when the resulting path will be be embedded
    /// in wrapper itself. I.e. a canonical path only ever contains one wrapper.
    #[logfn_inputs(TRACE)]
    fn remove_initial_value_wrapper(&self) -> Rc<Path> {
        match &self.value {
            PathEnum::Computed { value } => {
                if let Expression::InitialParameterValue { path, .. } = &value.expression {
                    path.clone()
                } else {
                    self.clone()
                }
            }
            PathEnum::Offset { value } => {
                if let Expression::Offset { left, right } = &value.expression {
                    if let Expression::InitialParameterValue { path, var_type } = &left.expression {
                        let unwrapped_left =
                            AbstractValue::make_typed_unknown(*var_type, path.clone());
                        let unwrapped_offset = unwrapped_left.offset(right.clone());
                        return Path::get_as_path(unwrapped_offset);
                    }
                }
                self.clone()
            }
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                let qualifier = qualifier.remove_initial_value_wrapper();
                Path::new_qualified(qualifier, selector.clone())
            }
            _ => self.clone(),
        }
    }

    /// Returns a copy path with the root replaced by new_root.
    #[logfn_inputs(TRACE)]
    fn replace_root(&self, old_root: &Rc<Path>, new_root: Rc<Path>) -> Rc<Path> {
        if *self == *old_root {
            return new_root;
        }
        match &self.value {
            PathEnum::Computed { value } => {
                Path::new_computed(value.replace_embedded_path_root(old_root, new_root))
            }
            PathEnum::Offset { value } => {
                if let Expression::Offset { left, right } = &value.expression {
                    let replaced_left = left.replace_embedded_path_root(old_root, new_root);
                    Path::get_as_path(replaced_left.offset(right.clone()))
                } else {
                    assume_unreachable!(
                        "PathEnum::Offset has value that is not Expression::Offset"
                    );
                }
            }
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

    /// Returns a copy of path with the selector replaced by the new selector.
    /// If the path is unqualified, returns self qualified with the new selector.
    #[logfn_inputs(TRACE)]
    fn add_or_replace_selector(&self, new_selector: Rc<PathSelector>) -> Rc<Path> {
        match &self.value {
            PathEnum::QualifiedPath { qualifier, .. } => {
                Path::new_qualified(qualifier.clone(), new_selector)
            }
            _ => Path::new_qualified(self.clone(), new_selector),
        }
    }

    /// Returns a copy of self with its last selector removed if that matches the given selector.
    #[logfn_inputs(TRACE)]
    fn remove_selector(&self, selector: Rc<PathSelector>) -> Rc<Path> {
        match &self.value {
            PathEnum::QualifiedPath {
                qualifier,
                selector: s,
                ..
            } if selector.eq(s) => {
                return qualifier.clone();
            }
            _ => {}
        }
        self.clone()
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

    /// Selects the function associated with a closure. Simple function values also
    /// use this so that all calls of a value find the function to call via this selector.
    Function,

    /// Select the struct field with the given index.
    Field(usize),

    /// Selects a particular type case from a type union.
    /// When updating the environment via such a field, all type cases need to be updated,
    /// hence the explicit mention of the number of cases.
    UnionField { case_index: usize, num_cases: usize },

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
        offset: u64,
        /// thing being indexed must be at least this long
        min_length: u64,
        /// counting backwards from end?
        from_end: bool,
    },

    /// These indices are generated by slice patterns.
    ///
    /// If `from_end` is true `slice[from..slice.len() - to]`.
    /// Otherwise `array[from..to]`.
    ConstantSlice { from: u64, to: u64, from_end: bool },

    /// "Downcast" to a variant of an ADT. Currently, MIR only introduces
    /// this for ADTs with more than one variant. The value is the ordinal of the variant.
    Downcast(Rc<str>, usize),

    /// Select the struct model field with the given name.
    /// A model field is a specification construct used during MIRAI verification
    /// and does not have a runtime location.
    ModelField(Rc<str>),

    /// Select the tag field of a non-scalar value.
    /// Similar to model fields, the tag field is a verification-specific construct and it
    /// does not have a runtime location.
    TagField,
}

impl Debug for PathSelector {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            PathSelector::Layout => f.write_str("layout"),
            PathSelector::Deref => f.write_str("deref"),
            PathSelector::Discriminant => f.write_str("discr"),
            PathSelector::Function => f.write_str("func"),
            PathSelector::Field(index) => index.fmt(f),
            PathSelector::UnionField {
                case_index,
                num_cases,
            } => f.write_fmt(format_args!("({:?} of {:?})", case_index, num_cases)),
            PathSelector::Index(value) => {
                if value.expression_size > 100 {
                    f.write_fmt(format_args!("[...]"))
                } else {
                    f.write_fmt(format_args!("[{:?}]", value))
                }
            }
            PathSelector::Slice(value) => f.write_fmt(format_args!("[0..{:?}]", value)),
            PathSelector::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => f.write_fmt(format_args!(
                "[offset: {}, min_length: {}, from_end: {}]",
                offset, min_length, from_end
            )),
            PathSelector::ConstantSlice { from, to, from_end } => {
                f.write_fmt(format_args!("[{} : {}, from_end: {}]", from, to, from_end))
            }
            PathSelector::Downcast(name, index) => {
                f.write_fmt(format_args!("as {}({})", name, *index))
            }
            PathSelector::ModelField(name) => name.fmt(f),
            PathSelector::TagField => f.write_str("$tag"),
        }
    }
}

impl PathSelector {
    /// Returns an abstract value for "true if the self selects the same runtime location as other"
    #[logfn_inputs(TRACE)]
    pub fn equals(&self, other: &Rc<PathSelector>) -> Rc<AbstractValue> {
        if self.eq(other) {
            return Rc::new(abstract_value::TRUE);
        }
        return match (self, other.as_ref()) {
            (PathSelector::Index(v1), PathSelector::Index(v2))
            | (PathSelector::Slice(v1), PathSelector::Slice(v2)) => v1.equals(v2.clone()),
            _ => Rc::new(abstract_value::FALSE),
        };
    }

    /// Adds any abstract heap addresses found in embedded index values to the given set.
    #[logfn_inputs(TRACE)]
    pub fn record_heap_blocks_and_strings(&self, result: &mut HashSet<Rc<AbstractValue>>) {
        match self {
            PathSelector::Index(value) | PathSelector::Slice(value) => {
                value.record_heap_blocks_and_strings(result);
            }
            _ => (),
        }
    }
}

pub trait PathSelectorRefinement: Sized {
    /// Refine parameters inside embedded index values with the given arguments.
    #[must_use]
    fn refine_parameters_and_paths(
        &self,
        args: &[(Rc<Path>, Rc<AbstractValue>)],
        result: &Option<Rc<Path>>,
        pre_env: &Environment,
        post_env: &Environment,
        fresh: usize,
    ) -> Self;
}

impl PathSelectorRefinement for Rc<PathSelector> {
    /// Refine parameters inside embedded index values with the given arguments.
    #[logfn_inputs(TRACE)]
    fn refine_parameters_and_paths(
        &self,
        args: &[(Rc<Path>, Rc<AbstractValue>)],
        result: &Option<Rc<Path>>,
        pre_env: &Environment,
        post_env: &Environment,
        fresh: usize,
    ) -> Rc<PathSelector> {
        match self.as_ref() {
            PathSelector::Index(value) => {
                let refined_value =
                    value.refine_parameters_and_paths(args, result, pre_env, post_env, fresh);
                Rc::new(PathSelector::Index(refined_value))
            }
            PathSelector::Slice(value) => {
                let refined_value =
                    value.refine_parameters_and_paths(args, result, pre_env, post_env, fresh);
                Rc::new(PathSelector::Slice(refined_value))
            }
            _ => self.clone(),
        }
    }
}
