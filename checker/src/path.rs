// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//
use crate::abstract_value::{self, AbstractValue, AbstractValueTrait};
use crate::constant_domain::ConstantDomain;
use crate::environment::Environment;
use crate::expression::{Expression, ExpressionType};
use crate::{k_limits, type_visitor, utils};

use log_derive::*;
use mirai_annotations::*;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
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
    pub fn get_as_path(value: Rc<AbstractValue>) -> Rc<Path> {
        Rc::new(match &value.expression {
            Expression::Cast { operand, .. } => {
                return Path::get_as_path(operand.clone());
            }
            Expression::HeapBlock { .. } => PathEnum::HeapBlock { value }.into(),
            Expression::Offset { .. } => PathEnum::Offset { value }.into(),
            Expression::UninterpretedCall { path, .. }
            | Expression::Variable { path, .. }
            | Expression::Widen { path, .. } => path.as_ref().clone(),
            _ => PathEnum::Alias { value }.into(),
        })
    }

    /// When splitting paths while doing weak updates, it is important to not refine paths because
    /// they are already canonical and because doing so can lead to recursive loops as refined paths
    /// re-introduce joined paths that have been split earlier.
    /// A split path, however, can be serve as the qualifier of a newly constructed qualified path
    /// and the qualified path might not be canonical. This routine tries to remove the two sources of
    /// de-canonicalization that are currently know. Essentially: when a path that binds to a value
    /// that is a reference is implicitly dereferenced by the selector, the canonical path will
    /// be the one without the reference, or the actual heap block, if the path binds to a heap
    /// location. This routine returns a re-canonicalized path in the two scenarios above,
    /// otherwise returns `None`.
    ///
    /// If the function returns a re-canonicalized path, which is used as the qualifier of a newly
    /// constructed qualified path, the caller of this function should check if the selector of the
    /// qualified path is `PathSelector::Deref`. If so, the deref selector should also be removed.
    #[logfn_inputs(DEBUG)]
    pub fn try_to_dereference(path: &Rc<Path>, environment: &Environment) -> Option<Rc<Path>> {
        if let PathEnum::Alias { value } = &path.value {
            if let Expression::Reference(path) = &value.expression {
                return Some(path.clone());
            }
        } else if let Some(value) = environment.value_map.get(path) {
            if let Expression::HeapBlock { .. } = &value.expression {
                return Some(Path::get_as_path(value.clone()));
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
    /// A path to a value that is not stored at a single memory location.
    /// For example, a compile time constant will not have a location.
    /// Another example is a conditional value with is either a parameter or a local variable,
    /// depending on a condition.
    /// In general, such a paths is needed when the value is an argument to a function call and
    /// the corresponding parameter shows up in the function summary as part of a path (usually a
    /// qualifier). In order to replace the parameter with the argument value, we need a path that
    /// wraps the argument value. When the value thus wrapped contains a reference to another path
    /// (or paths), the wrapper path is an alias to those paths.
    Alias { value: Rc<AbstractValue> },

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
            PathEnum::Alias { value } => value.fmt(f),
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
    /// Returns true if the path contains a value whose expression contains a local variable.
    #[logfn_inputs(TRACE)]
    pub fn contains_local_variable(&self) -> bool {
        match &self.value {
            PathEnum::Alias { value } => value.expression.contains_local_variable(),
            PathEnum::HeapBlock { .. } => true,
            PathEnum::LocalVariable { .. } => true,
            PathEnum::Offset { value } => value.expression.contains_local_variable(),
            PathEnum::Parameter { .. } => false,
            PathEnum::Result => false,
            PathEnum::StaticVariable { .. } => false,
            PathEnum::PhantomData => false,
            PathEnum::PromotedConstant { .. } => true,
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                qualifier.contains_local_variable() || {
                    if let PathSelector::Index(value) = selector.as_ref() {
                        value.expression.contains_local_variable()
                    } else {
                        false
                    }
                }
            }
        }
    }

    /// Returns the index value of the index path qualifed by qualifier.
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

    /// Returns the path to the first leaf field of the structure described by result_rustc_type.
    /// A field that is of type struct, is not a leaf field.
    #[logfn(TRACE)]
    pub fn get_path_to_field_at_offset_0<'tcx>(
        tcx: TyCtxt<'tcx>,
        environment: &Environment,
        path: &Rc<Path>,
        result_rustc_type: Ty<'tcx>,
    ) -> Option<Rc<Path>> {
        debug!(
            "get_path_to_field_at_offset_0 {:?} {:?}",
            path, result_rustc_type
        );
        match &result_rustc_type.kind {
            TyKind::Adt(def, substs) => {
                let path0 = Path::new_field(path.clone(), 0);
                for v in def.variants.iter() {
                    if let Some(field0) = v.fields.get(0) {
                        let field0_ty = field0.ty(tcx, substs);
                        let result = Self::get_path_to_field_at_offset_0(
                            tcx,
                            environment,
                            &path0,
                            field0_ty,
                        );
                        if result.is_some() {
                            return result;
                        }
                    }
                }
                if def.is_enum() {
                    let path0 = Path::new_discriminant(path.clone());
                    return Some(path0);
                }
                None
            }
            TyKind::Tuple(substs) => {
                if let Some(field0_ty) = substs.iter().map(|s| s.expect_ty()).next() {
                    let path0 = Path::new_field(path.clone(), 0);
                    return Self::get_path_to_field_at_offset_0(
                        tcx,
                        environment,
                        &path0,
                        field0_ty,
                    );
                }
                None
            }
            _ => Some(path.clone()),
        }
    }

    /// Returns the path to the first leaf field of the structure described by path_rustc_type.
    /// A field that is of type struct, is not a leaf field.
    /// The field at offset 0 must be a thin pointer.
    #[logfn(TRACE)]
    pub fn get_path_to_thin_pointer_at_offset_0<'tcx>(
        tcx: TyCtxt<'tcx>,
        environment: &Environment,
        path: &Rc<Path>,
        path_rustc_type: Ty<'tcx>,
    ) -> Option<Rc<Path>> {
        trace!(
            "get_path_to_thin_pointer_at_offset_0 {:?} {:?}",
            path,
            path_rustc_type
        );
        match &path_rustc_type.kind {
            TyKind::Ref(..) | TyKind::RawPtr(..) => {
                if type_visitor::is_slice_pointer(&path_rustc_type.kind) {
                    Some(Path::new_field(path.clone(), 0))
                } else {
                    Some(path.clone())
                }
            }
            TyKind::Adt(def, substs) => {
                let path0 = Path::new_field(path.clone(), 0);
                for v in def.variants.iter() {
                    if let Some(field0) = v.fields.get(0) {
                        let field0_ty = field0.ty(tcx, substs);
                        let result = Self::get_path_to_thin_pointer_at_offset_0(
                            tcx,
                            environment,
                            &path0,
                            field0_ty,
                        );
                        if result.is_some() {
                            return result;
                        }
                    }
                }
                None
            }
            TyKind::Tuple(substs) => {
                if let Some(field0_ty) = substs.iter().map(|s| s.expect_ty()).next() {
                    let path0 = Path::new_field(path.clone(), 0);
                    return Self::get_path_to_thin_pointer_at_offset_0(
                        tcx,
                        environment,
                        &path0,
                        field0_ty,
                    );
                }
                None
            }
            _ => None,
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

    /// Creates a path that aliases once or more paths contained inside the value.
    #[logfn_inputs(TRACE)]
    pub fn new_alias(value: Rc<AbstractValue>) -> Rc<Path> {
        Rc::new(PathEnum::Alias { value }.into())
    }

    /// Creates a path to the target memory of a reference value.
    #[logfn_inputs(TRACE)]
    pub fn new_deref(address_path: Rc<Path>) -> Rc<Path> {
        let selector = Rc::new(PathSelector::Deref);
        Self::new_qualified(address_path, selector)
    }

    /// Creates a path the selects the discriminant of the enum at the given path.
    #[logfn_inputs(TRACE)]
    pub fn new_discriminant(enum_path: Rc<Path>) -> Rc<Path> {
        let selector = Rc::new(PathSelector::Discriminant);
        Self::new_qualified(enum_path, selector)
    }

    /// Creates a path the selects the given field of the struct at the given path.
    #[logfn_inputs(TRACE)]
    pub fn new_field(qualifier: Rc<Path>, field_index: usize) -> Rc<Path> {
        let selector = Rc::new(PathSelector::Field(field_index));
        Self::new_qualified(qualifier, selector)
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
                expression_type: ExpressionType::from(&ty.kind),
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
    pub fn new_length(array_path: Rc<Path>) -> Rc<Path> {
        let selector = Rc::new(PathSelector::Field(1));
        Self::new_qualified(array_path, selector)
    }

    /// Creates a path the selects the given model field of the value at the given path.
    #[logfn_inputs(TRACE)]
    pub fn new_model_field(qualifier: Rc<Path>, field_name: Rc<String>) -> Rc<Path> {
        let selector = Rc::new(PathSelector::ModelField(field_name));
        Self::new_qualified(qualifier, selector)
    }

    /// Creates a path the qualifies the given root path with the given selector.
    #[logfn_inputs(TRACE)]
    pub fn new_qualified(qualifier: Rc<Path>, selector: Rc<PathSelector>) -> Rc<Path> {
        if let PathEnum::Alias { value } = &qualifier.value {
            // A path that is an alias for bottom must stay that way even if qualified by a selector.
            if value.is_bottom() {
                return qualifier;
            }

            // A path that is an alias for a & operation must simplify when dereferenced
            // in order to stay canonical.
            // Note that the tricky semantics of constructing a copy of struct when doing *&x
            // is taken care of when handling the MIR operation and paths need not be concerned with it.
            if let Expression::Reference(path) = &value.expression {
                if matches!(selector.as_ref(), PathSelector::Deref) {
                    return path.clone();
                }
            }
        }
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

    /// Returns a copy of self with the root replaced by new_root.
    fn replace_root(&self, old_root: &Rc<Path>, new_root: Rc<Path>) -> Rc<Path>;

    /// Returns a copy of self with the selector replace by a new selector.
    /// It is only legal to call this on a qualfied path.
    fn replace_selector(&self, new_selector: Rc<PathSelector>) -> Rc<Path>;
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
                if (*ordinal) != 999 {
                    // This is a handy place to put a break point.
                    let _x = *ordinal;
                }
                Path::new_local((*ordinal) + fresh)
            }
            PathEnum::Offset { value } => {
                Path::get_as_path(value.refine_parameters(arguments, fresh))
            }
            PathEnum::Parameter { ordinal } => {
                if *ordinal > arguments.len() {
                    debug!("Summary refers to a parameter that does not have a matching argument");
                    Path::new_alias(Rc::new(abstract_value::BOTTOM))
                } else {
                    arguments[*ordinal - 1].0.clone()
                }
            }
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
    /// we want to remove the reference from the qualifier in order to normalize the path
    /// and not have more than one path for the same location.
    #[logfn_inputs(TRACE)]
    fn refine_paths(&self, environment: &Environment) -> Rc<Path> {
        if let Some(val) = environment.value_at(&self) {
            if val.refers_to_unknown_location() {
                // self is an alias for val
                return Path::get_as_path(val.clone());
            }
        };
        // self is a path that is not a key in the environment. This could be because it is not
        // canonical.
        match &self.value {
            PathEnum::Alias { value } => {
                if value.refers_to_unknown_location() {
                    Path::get_as_path(value.clone())
                } else {
                    self.clone()
                }
            }
            PathEnum::Offset { value } => {
                checked_assume!(matches!(&value.expression, Expression::Offset{..}));
                Path::get_as_path(value.refine_paths(environment))
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
                if let PathEnum::Alias { value } = &refined_qualifier.value {
                    if *refined_selector.as_ref() == PathSelector::Deref {
                        if let Expression::Reference(path) = &value.expression {
                            // *&path during refinement just becomes path
                            return path.clone();
                        }
                    }
                    if let Expression::Reference(path) = &value.expression {
                        // since self is a qualified path we have to drop the reference operator
                        // since selectors implicitly dereference pointers.
                        return Path::new_qualified(path.clone(), refined_selector);
                    }
                }
                if let PathSelector::Downcast(_, variant) = refined_selector.as_ref() {
                    let discriminator = Path::new_discriminant(refined_qualifier.clone());
                    if let Some(val) = environment.value_at(&discriminator) {
                        if let Expression::CompileTimeConstant(ConstantDomain::U128(ordinal)) =
                            &val.expression
                        {
                            if (*variant as u128) != *ordinal {
                                // The downcast is impossible in this calling context
                                return Path::new_alias(Rc::new(abstract_value::BOTTOM));
                            }
                        }
                    }
                }
                if let Some(val) = environment.value_at(&refined_qualifier) {
                    match &val.expression {
                        Expression::CompileTimeConstant(ConstantDomain::Str(..))
                        | Expression::HeapBlock { .. } => {
                            if *refined_selector.as_ref() == PathSelector::Deref {
                                return Path::new_qualified(
                                    Path::get_as_path(val.clone()),
                                    refined_selector,
                                );
                            }
                        }
                        Expression::Variable { path, .. } => {
                            return Path::new_qualified(path.clone(), refined_selector);
                        }
                        _ => {
                            if val.refers_to_unknown_location() {
                                return Path::new_qualified(
                                    Path::get_as_path(val.clone()),
                                    refined_selector,
                                );
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

    /// Returns a copy path with the root replaced by new_root.
    #[logfn_inputs(TRACE)]
    fn replace_selector(&self, new_selector: Rc<PathSelector>) -> Rc<Path> {
        match &self.value {
            PathEnum::QualifiedPath { qualifier, .. } => {
                Path::new_qualified(qualifier.clone(), new_selector)
            }
            _ => assume_unreachable!("don't call this on an unqualified path"),
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
