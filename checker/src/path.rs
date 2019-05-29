// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//
use crate::abstract_value::AbstractValue;
use crate::abstract_value::AbstractValueTrait;
use crate::environment::Environment;
use crate::expression::{Expression, ExpressionType};

use mirai_annotations::assume;
use rustc::hir::def_id::DefId;
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::rc::Rc;

/// A path represents a left hand side expression.
/// When the actual expression is evaluated at runtime it will resolve to a particular memory
/// location. During analysis it is used to keep track of state changes.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Path {
    /// A dynamically allocated memory block.
    AbstractHeapAddress { ordinal: usize },

    /// Sometimes a constant value needs to be treated as a path during refinement.
    /// Don't use this unless you are really sure you know what you are doing.
    Constant { value: Rc<AbstractValue> },

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
        summary_cache_key: Rc<String>,
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
        qualifier: Rc<Path>,
        selector: Rc<PathSelector>,
    },
}

impl Path {
    /// True if path qualifies root, or another qualified path rooted by root.
    pub fn is_rooted_by(&self, root: &Rc<Path>) -> bool {
        match self {
            Path::QualifiedPath { qualifier, .. } => {
                *qualifier == *root || qualifier.is_rooted_by(root)
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
}

pub trait PathRefinement: Sized {
    /// Refine parameters inside embedded index values with the given arguments.
    fn refine_parameters(&self, arguments: &[(Rc<Path>, Rc<AbstractValue>)]) -> Rc<Path>;

    /// Refine paths that reference other paths.
    /// I.e. when a reference is passed to a function that then returns
    /// or leaks it back to the caller in the qualifier of a path then
    /// we want to dereference the qualifier in order to normalize the path
    /// and not have more than one path for the same location.
    fn refine_paths(&self, environment: &mut Environment) -> Rc<Path>;

    /// Returns a copy path with the root replaced by new_root.
    fn replace_root(&self, old_root: &Rc<Path>, new_root: Rc<Path>) -> Rc<Path>;
}

impl PathRefinement for Rc<Path> {
    /// Refine parameters inside embedded index values with the given arguments.
    fn refine_parameters(&self, arguments: &[(Rc<Path>, Rc<AbstractValue>)]) -> Rc<Path> {
        match self.as_ref() {
            Path::LocalVariable { ordinal } if 0 < *ordinal && *ordinal <= arguments.len() => {
                arguments[*ordinal - 1].0.clone()
            }
            Path::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                let refined_qualifier = qualifier.refine_parameters(arguments);
                let refined_selector = selector.refine_parameters(arguments);
                let refined_length = refined_qualifier.path_length();
                assume!(refined_length < 1_000_000_000); // We'll run out of memory long before this happens
                Rc::new(Path::QualifiedPath {
                    qualifier: refined_qualifier,
                    selector: refined_selector,
                    length: refined_length + 1,
                })
            }
            _ => self.clone(),
        }
    }

    /// Refine paths that reference other paths.
    /// I.e. when a reference is passed to a function that then returns
    /// or leaks it back to the caller in the qualifier of a path then
    /// we want to dereference the qualifier in order to normalize the path
    /// and not have more than one path for the same location.
    fn refine_paths(&self, environment: &mut Environment) -> Rc<Path> {
        if let Some(val) = environment.value_at(&self) {
            // if the environment has self as a key, then self is canonical,
            // except if val is a Reference to another path.
            return match &val.expression {
                Expression::Reference(dereferenced_path) => dereferenced_path.clone(),
                _ => self.clone(),
            };
        };
        if let Path::QualifiedPath {
            qualifier,
            selector,
            length,
        } = self.as_ref()
        {
            if let Some(val) = environment.value_at(qualifier) {
                match &val.expression {
                    Expression::Reference(dereferenced_path) => {
                        // The qualifier is being dereferenced, so if the value at qualifier
                        // is an explicit reference to another path, put the other path in the place
                        // of qualifier since references do not own elements directly in
                        // the environment.
                        let path_len = dereferenced_path.path_length();
                        assume!(path_len < 1_000_000_000); // We'll run out of memory long before this happens
                        Rc::new(Path::QualifiedPath {
                            qualifier: dereferenced_path.clone(),
                            selector: selector.clone(),
                            length: path_len + 1,
                        })
                    }
                    _ => {
                        // Although the qualifier matches an expression, that expression
                        // is too abstract too qualify the path sufficiently that we
                        // can refine this value.
                        Rc::new(Path::QualifiedPath {
                            qualifier: qualifier.clone(),
                            selector: selector.clone(),
                            length: *length,
                        })
                    }
                }
            } else {
                // The qualifier does not match a value in the environment, but parts of it might.
                // Reminder, a path that does not match a value in the environment is rooted in
                // an unknown value, such as a parameter.
                let refined_qualifier = qualifier.refine_paths(environment);
                let refined_qualifier_matches =
                    environment.value_map.contains_key(&refined_qualifier);
                let refined_selector = selector.refine_paths(environment);
                let refined_length = refined_qualifier.path_length();
                assume!(refined_length < 1_000_000_000); // We'll run out of memory long before this happens
                let refined_path = Rc::new(Path::QualifiedPath {
                    qualifier: refined_qualifier,
                    selector: refined_selector,
                    length: refined_length + 1,
                });
                if refined_qualifier_matches {
                    refined_path.refine_paths(environment)
                } else {
                    refined_path
                }
            }
        } else {
            self.clone()
        }
    }

    /// Returns a copy path with the root replaced by new_root.
    fn replace_root(&self, old_root: &Rc<Path>, new_root: Rc<Path>) -> Rc<Path> {
        match self.as_ref() {
            Path::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                let new_qualifier = if *qualifier == *old_root {
                    new_root
                } else {
                    qualifier.replace_root(old_root, new_root)
                };
                let new_qualifier_path_length = new_qualifier.path_length();
                assume!(new_qualifier_path_length < 1_000_000_000); // We'll run out of memory long before this happens
                Rc::new(Path::QualifiedPath {
                    qualifier: new_qualifier,
                    selector: selector.clone(),
                    length: new_qualifier_path_length + 1,
                })
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

    /// The tag used to indicate which case of an enum is used for a particular enum value.
    Discriminant,

    /// Select the struct field with the given index.
    Field(usize),

    /// Select the collection element with the index specified by the abstract value.
    Index(Rc<AbstractValue>),

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

    /// Select the struct model field with the given name.
    /// A model field is a specification construct used during MIRAI verification
    /// and does not have a runtime location.
    ModelField(Rc<String>),
}

impl PathSelector {
    /// Adds any abstract heap addresses found in embedded index values to the given set.
    pub fn record_heap_addresses(&self, result: &mut HashSet<usize>) {
        if let PathSelector::Index(value) = self {
            value.record_heap_addresses(result);
        }
    }
}

pub trait PathSelectorRefinement: Sized {
    /// Refine parameters inside embedded index values with the given arguments.
    fn refine_parameters(&self, arguments: &[(Rc<Path>, Rc<AbstractValue>)]) -> Self;

    /// Returns a value that is simplified (refined) by replacing values with Variable(path) expressions
    /// with the value at that path (if there is one). If no refinement is possible
    /// the result is simply a clone of this value. This refinement only makes sense
    /// following a call to refine_parameters.
    fn refine_paths(&self, environment: &mut Environment) -> Self;
}

impl PathSelectorRefinement for Rc<PathSelector> {
    /// Refine parameters inside embedded index values with the given arguments.
    fn refine_parameters(&self, arguments: &[(Rc<Path>, Rc<AbstractValue>)]) -> Rc<PathSelector> {
        if let PathSelector::Index(value) = self.as_ref() {
            let refined_value = value.refine_parameters(arguments);
            Rc::new(PathSelector::Index(refined_value))
        } else {
            self.clone()
        }
    }

    /// Returns a value that is simplified (refined) by replacing values with Variable(path) expressions
    /// with the value at that path (if there is one). If no refinement is possible
    /// the result is simply a clone of this value. This refinement only makes sense
    /// following a call to refine_parameters.
    fn refine_paths(&self, environment: &mut Environment) -> Rc<PathSelector> {
        if let PathSelector::Index(value) = self.as_ref() {
            let refined_value = value.refine_paths(environment);
            Rc::new(PathSelector::Index(refined_value))
        } else {
            self.clone()
        }
    }
}
