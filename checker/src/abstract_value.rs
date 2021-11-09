// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

#![allow(clippy::declare_interior_mutable_const)]
use crate::bool_domain::BoolDomain;
use crate::constant_domain::ConstantDomain;
use crate::environment::Environment;
use crate::expression::Expression::{ConditionalExpression, Join};
use crate::expression::{Expression, ExpressionType};
use crate::interval_domain::{self, IntervalDomain};
use crate::k_limits;
use crate::path::{Path, PathEnum, PathSelector};
use crate::path::{PathRefinement, PathRoot};
use crate::tag_domain::{Tag, TagDomain};

use crate::known_names::KnownNames;
use log_derive::{logfn, logfn_inputs};
use mirai_annotations::*;
use serde::{Deserialize, Serialize};
use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt::{Debug, Formatter, Result};
use std::hash::Hash;
use std::hash::Hasher;
use std::rc::Rc;

// See https://github.com/facebookexperimental/MIRAI/blob/main/documentation/AbstractValues.md.

/// Mirai is an abstract interpreter and thus produces abstract values.
/// In general, an abstract value is a value that is not fully known.
/// For example, we may know that it is a number between 1 and 10, but not
/// which particular number.
///
/// When we do know everything about a value, it is concrete rather than
/// abstract, but is convenient to just use this structure for concrete values
/// as well, since all operations can be uniform.
#[derive(Serialize, Deserialize, Clone, Eq, Ord, PartialOrd)]
pub struct AbstractValue {
    // This is not a domain element, but a representation of how this value has been constructed.
    // It is used to refine the value with respect to path conditions and actual arguments.
    // It is also used to construct corresponding domain elements, when needed.
    pub expression: Expression,
    // Keeps track of how large the expression is.
    // When an expression gets too large it needs to get widened otherwise execution time diverges.
    pub expression_size: u64,
    /// Cached interval domain element computed on demand by get_as_interval.
    #[serde(skip)]
    interval: RefCell<Option<Rc<IntervalDomain>>>,
    #[serde(skip)]
    /// Cached optional bool that if present and true, indicates that this value is a pointer
    /// or reference that is known at compile time to be non null.
    is_non_null: RefCell<Option<bool>>,
    /// Cached tag domain element computed on demand by get_tags.
    #[serde(skip)]
    tags: RefCell<Option<Rc<TagDomain>>>,
}

impl Debug for AbstractValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.expression.fmt(f)
    }
}

/// Make a new value from the given expression, using defaults for all other fields.
const fn make_value(e: Expression) -> AbstractValue {
    AbstractValue {
        expression: e,
        expression_size: 1,
        interval: RefCell::new(None),
        is_non_null: RefCell::new(None),
        tags: RefCell::new(None),
    }
}

impl Hash for AbstractValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.expression.hash(state);
    }
}

impl PartialEq for AbstractValue {
    #[logfn_inputs(TRACE)]
    fn eq(&self, other: &Self) -> bool {
        self.expression.eq(&other.expression)
    }
}

/// An abstract domain element that all represent the impossible concrete value.
/// I.e. the corresponding set of possible concrete values is empty.
pub const BOTTOM: AbstractValue = make_value(Expression::Bottom);

/// An abstract domain element that all represent the single concrete value, false.
pub const FALSE: AbstractValue = make_value(Expression::CompileTimeConstant(ConstantDomain::False));

/// An abstract domain element that all represents all possible concrete values.
pub const TOP: AbstractValue = make_value(Expression::Top);

/// An abstract domain element that all represent the single concrete value, true.
pub const TRUE: AbstractValue = make_value(Expression::CompileTimeConstant(ConstantDomain::True));

/// An abstract domain element that represents a dummy untagged value.
/// It is only used as the default value for the tag field of non-scalar values.
pub const DUMMY_UNTAGGED_VALUE: AbstractValue =
    make_value(Expression::CompileTimeConstant(ConstantDomain::I128(0)));

impl From<bool> for AbstractValue {
    #[logfn_inputs(TRACE)]
    fn from(b: bool) -> AbstractValue {
        if b {
            TRUE
        } else {
            FALSE
        }
    }
}

impl From<ConstantDomain> for AbstractValue {
    #[logfn_inputs(TRACE)]
    fn from(cv: ConstantDomain) -> AbstractValue {
        if let ConstantDomain::Bottom = &cv {
            BOTTOM
        } else {
            make_value(Expression::CompileTimeConstant(cv))
        }
    }
}

impl From<BoolDomain> for AbstractValue {
    #[logfn_inputs(TRACE)]
    fn from(b: BoolDomain) -> AbstractValue {
        match b {
            BoolDomain::Bottom => BOTTOM,
            BoolDomain::True => TRUE,
            BoolDomain::False => FALSE,
            BoolDomain::Top => TOP,
        }
    }
}

impl From<i128> for AbstractValue {
    #[logfn_inputs(TRACE)]
    fn from(cv: i128) -> AbstractValue {
        make_value(Expression::CompileTimeConstant(ConstantDomain::I128(cv)))
    }
}

impl From<u128> for AbstractValue {
    #[logfn_inputs(TRACE)]
    fn from(cv: u128) -> AbstractValue {
        make_value(Expression::CompileTimeConstant(ConstantDomain::U128(cv)))
    }
}

impl AbstractValue {
    /// Creates an abstract value from a binary expression and keeps track of the size.
    #[logfn_inputs(TRACE)]
    fn make_binary(
        mut left: Rc<AbstractValue>,
        mut right: Rc<AbstractValue>,
        operation: fn(Rc<AbstractValue>, Rc<AbstractValue>) -> Expression,
    ) -> Rc<AbstractValue> {
        if left.is_top() || left.is_bottom() {
            return left;
        }
        if right.is_top() || right.is_bottom() {
            return right;
        }
        let mut expression_size = left.expression_size.saturating_add(right.expression_size);
        if expression_size > k_limits::MAX_EXPRESSION_SIZE {
            // The overall expression is going to overflow, so pre-compute the simpler domains from
            // the larger expression and then replace its expression with TOP.
            if left.expression_size < right.expression_size {
                debug!("binary expression right operand abstracted {:?}", right);
                right = AbstractValue::make_from(right.expression.clone(), u64::MAX);
                expression_size = left.expression_size + 1;
            } else {
                debug!("binary expression left operand abstracted: {:?}", left);
                left = AbstractValue::make_from(left.expression.clone(), u64::MAX);
                expression_size = right.expression_size + 1;
            }
        }
        Self::make_from(operation(left, right), expression_size)
    }

    /// Creates an abstract value from a typed binary expression and keeps track of the size.
    #[logfn_inputs(TRACE)]
    fn make_typed_binary(
        mut left: Rc<AbstractValue>,
        mut right: Rc<AbstractValue>,
        result_type: ExpressionType,
        operation: fn(Rc<AbstractValue>, Rc<AbstractValue>, ExpressionType) -> Expression,
    ) -> Rc<AbstractValue> {
        if left.is_top() || left.is_bottom() {
            return left;
        }
        if right.is_top() || right.is_bottom() {
            return right;
        }
        let mut expression_size = left.expression_size.saturating_add(right.expression_size);
        if expression_size > k_limits::MAX_EXPRESSION_SIZE {
            // The overall expression is going to overflow, so pre-compute the simpler domains from
            // the larger expression and then replace its expression with TOP.
            if left.expression_size < right.expression_size {
                debug!("binary expression right operand abstracted {:?}", right);
                right = AbstractValue::make_from(right.expression.clone(), u64::MAX);
                expression_size = left.expression_size + 1;
            } else {
                debug!("binary expression left operand abstracted: {:?}", left);
                left = AbstractValue::make_from(left.expression.clone(), u64::MAX);
                expression_size = right.expression_size + 1;
            }
        }
        Self::make_from(operation(left, right, result_type), expression_size)
    }

    /// Creates an abstract value from a typed unary expression and keeps track of the size.
    #[logfn_inputs(TRACE)]
    fn make_typed_unary(
        operand: Rc<AbstractValue>,
        result_type: ExpressionType,
        operation: fn(Rc<AbstractValue>, ExpressionType) -> Expression,
    ) -> Rc<AbstractValue> {
        if operand.is_top() || operand.is_bottom() {
            return operand;
        }
        let expression_size = operand.expression_size.saturating_add(1);
        Self::make_from(operation(operand, result_type), expression_size)
    }

    /// Creates an abstract value from a unary expression and keeps track of the size.
    #[logfn_inputs(TRACE)]
    fn make_unary(
        operand: Rc<AbstractValue>,
        operation: fn(Rc<AbstractValue>) -> Expression,
    ) -> Rc<AbstractValue> {
        if operand.is_top() || operand.is_bottom() {
            return operand;
        }
        let expression_size = operand.expression_size.saturating_add(1);
        Self::make_from(operation(operand), expression_size)
    }

    /// Creates an abstract value that represents a call to a function whose summary is not
    /// known at the time of the call. This is usually because the function has no MIR body,
    /// but can also be because the function is self recursive and thus gets called before it
    /// has been summarized.
    #[logfn_inputs(TRACE)]
    fn make_uninterpreted_call(
        callee: Rc<AbstractValue>,
        arguments: Vec<Rc<AbstractValue>>,
        result_type: ExpressionType,
        path: Rc<Path>,
    ) -> Rc<AbstractValue> {
        let expression_size = arguments.iter().fold(callee.expression_size, |acc, a| {
            acc.saturating_add(a.expression_size)
        });
        AbstractValue::make_from(
            Expression::UninterpretedCall {
                callee,
                arguments,
                result_type,
                path,
            },
            expression_size,
        )
    }

    /// Returns a tag check on `operand`. If we can decide the presence/absence of tag, return
    /// TRUE/FALSE. Otherwise, returns an unknown tag check.
    #[logfn_inputs(TRACE)]
    pub fn make_tag_check(
        operand: Rc<AbstractValue>,
        tag: Tag,
        checking_presence: bool,
    ) -> Rc<AbstractValue> {
        let check_value = if checking_presence {
            operand.has_tag(&tag)
        } else {
            operand.does_not_have_tag(&tag)
        };
        if check_value.is_top() {
            // Cannot refine this tag check to a known value. Return an unknown tag check.
            if checking_presence {
                operand.make_presence_check(tag)
            } else {
                operand.make_absence_check(tag)
            }
        } else {
            check_value
        }
    }

    #[logfn_inputs(DEBUG)]
    #[logfn(DEBUG)]
    fn make_presence_check(&self, tag: Tag) -> Rc<AbstractValue> {
        let exp_tag_prop_opt = self.expression.get_tag_propagation();

        // First deal with expressions that do not propagate tags or have special propagation behavior.
        match &self.expression {
            Expression::Top => {
                return Rc::new(self.clone());
            }

            Expression::Bottom
            | Expression::CompileTimeConstant { .. }
            | Expression::HeapBlock { .. }
            | Expression::HeapBlockLayout { .. }
            | Expression::UnknownTagCheck { .. } => {
                return Rc::new(FALSE);
            }

            Expression::InitialParameterValue { .. }
            | Expression::UnknownModelField { .. }
            | Expression::UnknownTagField { .. }
            | Expression::Variable { .. } => {
                let expression_size = self.expression_size.saturating_add(1);
                return AbstractValue::make_from(
                    Expression::UnknownTagCheck {
                        operand: Rc::new(self.clone()),
                        tag,
                        checking_presence: true,
                    },
                    expression_size,
                );
            }

            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => {
                return condition
                    .make_presence_check(tag)
                    .or(condition.conditional_expression(
                        consequent.make_presence_check(tag),
                        alternate.make_presence_check(tag),
                    ));
            }

            Expression::Join { left, right } => {
                return left
                    .make_presence_check(tag)
                    .join(right.make_presence_check(tag));
            }

            Expression::Switch {
                discriminator,
                cases,
                default,
            } => {
                // For each tag A, whether the switch expression has tag A or not is
                // (discriminator has tag A) or ((case_0 has tag A) join .. join (case_n has tag A) join (default has tag A)).
                let mut tags_from_cases = default.make_presence_check(tag);
                for case in cases {
                    tags_from_cases = tags_from_cases.or(case.1.make_presence_check(tag))
                }
                return discriminator.make_presence_check(tag).or(tags_from_cases);
            }

            Expression::TaggedExpression { operand, tag: t } => {
                return if tag.eq(t) {
                    Rc::new(TRUE)
                } else {
                    operand.make_presence_check(tag)
                }
            }

            Expression::WidenedJoin { operand, .. } => return operand.make_presence_check(tag),

            _ => {
                checked_assume!(exp_tag_prop_opt.is_some());
            }
        }

        let exp_tag_prop = exp_tag_prop_opt.unwrap();

        // Then deal with expressions that have standard propagation behavior, i.e., taking tags
        // from children nodes.
        match &self.expression {
            Expression::Add { left, right }
            | Expression::AddOverflows { left, right, .. }
            | Expression::And { left, right }
            | Expression::BitAnd { left, right }
            | Expression::BitOr { left, right }
            | Expression::BitXor { left, right }
            | Expression::Div { left, right }
            | Expression::Equals { left, right }
            | Expression::GreaterOrEqual { left, right }
            | Expression::GreaterThan { left, right }
            | Expression::IntrinsicBinary { left, right, .. }
            | Expression::LessOrEqual { left, right }
            | Expression::LessThan { left, right }
            | Expression::Mul { left, right }
            | Expression::MulOverflows { left, right, .. }
            | Expression::Ne { left, right }
            | Expression::Or { left, right }
            | Expression::Offset { left, right }
            | Expression::Rem { left, right }
            | Expression::Shl { left, right }
            | Expression::ShlOverflows { left, right, .. }
            | Expression::Shr { left, right, .. }
            | Expression::ShrOverflows { left, right, .. }
            | Expression::Sub { left, right }
            | Expression::SubOverflows { left, right, .. } => {
                if tag.is_propagated_by(exp_tag_prop) {
                    left.make_presence_check(tag)
                        .or(right.make_presence_check(tag))
                } else {
                    Rc::new(FALSE)
                }
            }

            Expression::BitNot { operand, .. }
            | Expression::Cast { operand, .. }
            | Expression::IntrinsicBitVectorUnary { operand, .. }
            | Expression::IntrinsicFloatingPointUnary { operand, .. }
            | Expression::LogicalNot { operand, .. }
            | Expression::Neg { operand, .. }
            | Expression::Transmute { operand, .. } => {
                if tag.is_propagated_by(exp_tag_prop) {
                    operand.make_presence_check(tag)
                } else {
                    Rc::new(FALSE)
                }
            }

            Expression::Memcmp {
                left,
                right,
                length,
            } => {
                if tag.is_propagated_by(exp_tag_prop) {
                    left.make_presence_check(tag)
                        .or(right.make_presence_check(tag))
                        .or(length.make_presence_check(tag))
                } else {
                    Rc::new(FALSE)
                }
            }

            Expression::UninterpretedCall {
                callee, arguments, ..
            } => {
                if tag.is_propagated_by(exp_tag_prop) {
                    let mut check = callee.make_presence_check(tag);
                    for argument in arguments {
                        check = check.or(argument.make_presence_check(tag))
                    }
                    check
                } else {
                    Rc::new(FALSE)
                }
            }

            _ => {
                verify_unreachable!();
            }
        }
    }

    #[logfn_inputs(DEBUG)]
    #[logfn(DEBUG)]
    fn make_absence_check(&self, tag: Tag) -> Rc<AbstractValue> {
        let exp_tag_prop_opt = self.expression.get_tag_propagation();

        // First deal with expressions that do not propagate tags or have special propagation behavior.
        match &self.expression {
            Expression::Top => {
                return Rc::new(self.clone());
            }

            Expression::Bottom
            | Expression::CompileTimeConstant { .. }
            | Expression::HeapBlock { .. }
            | Expression::HeapBlockLayout { .. }
            | Expression::UnknownTagCheck { .. } => {
                return Rc::new(TRUE);
            }

            Expression::InitialParameterValue { .. }
            | Expression::UnknownModelField { .. }
            | Expression::UnknownTagField { .. }
            | Expression::Variable { .. } => {
                let expression_size = self.expression_size.saturating_add(1);
                return AbstractValue::make_from(
                    Expression::UnknownTagCheck {
                        operand: Rc::new(self.clone()),
                        tag,
                        checking_presence: false,
                    },
                    expression_size,
                );
            }

            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => {
                return condition
                    .make_absence_check(tag)
                    .and(condition.conditional_expression(
                        consequent.make_absence_check(tag),
                        alternate.make_absence_check(tag),
                    ));
            }

            Expression::Join { left, right } => {
                return left
                    .make_absence_check(tag)
                    .join(right.make_absence_check(tag));
            }

            Expression::Switch {
                discriminator,
                cases,
                default,
            } => {
                // For each tag A, whether the switch expression has tag A or not is
                // (discriminator has tag A) or ((case_0 has tag A) join .. join (case_n has tag A) join (default has tag A)).
                let mut tags_from_cases = default.make_absence_check(tag);
                for case in cases {
                    tags_from_cases = tags_from_cases.and(case.1.make_absence_check(tag))
                }
                return discriminator.make_absence_check(tag).and(tags_from_cases);
            }

            Expression::TaggedExpression { operand, tag: t } => {
                return if tag.eq(t) {
                    Rc::new(FALSE)
                } else {
                    operand.make_absence_check(tag)
                }
            }

            Expression::WidenedJoin { operand, .. } => return operand.make_absence_check(tag),

            _ => {
                checked_assume!(exp_tag_prop_opt.is_some());
            }
        }

        let exp_tag_prop = exp_tag_prop_opt.unwrap();

        // Then deal with expressions that have standard propagation behavior, i.e., taking tags
        // from children nodes.
        match &self.expression {
            Expression::Add { left, right }
            | Expression::AddOverflows { left, right, .. }
            | Expression::And { left, right }
            | Expression::BitAnd { left, right }
            | Expression::BitOr { left, right }
            | Expression::BitXor { left, right }
            | Expression::Div { left, right }
            | Expression::Equals { left, right }
            | Expression::GreaterOrEqual { left, right }
            | Expression::GreaterThan { left, right }
            | Expression::IntrinsicBinary { left, right, .. }
            | Expression::LessOrEqual { left, right }
            | Expression::LessThan { left, right }
            | Expression::Mul { left, right }
            | Expression::MulOverflows { left, right, .. }
            | Expression::Ne { left, right }
            | Expression::Or { left, right }
            | Expression::Offset { left, right }
            | Expression::Rem { left, right }
            | Expression::Shl { left, right }
            | Expression::ShlOverflows { left, right, .. }
            | Expression::Shr { left, right, .. }
            | Expression::ShrOverflows { left, right, .. }
            | Expression::Sub { left, right }
            | Expression::SubOverflows { left, right, .. } => {
                if tag.is_propagated_by(exp_tag_prop) {
                    left.make_absence_check(tag)
                        .and(right.make_absence_check(tag))
                } else {
                    Rc::new(TRUE)
                }
            }

            Expression::BitNot { operand, .. }
            | Expression::Cast { operand, .. }
            | Expression::IntrinsicBitVectorUnary { operand, .. }
            | Expression::IntrinsicFloatingPointUnary { operand, .. }
            | Expression::LogicalNot { operand, .. }
            | Expression::Neg { operand, .. }
            | Expression::Transmute { operand, .. } => {
                if tag.is_propagated_by(exp_tag_prop) {
                    operand.make_absence_check(tag)
                } else {
                    Rc::new(TRUE)
                }
            }

            Expression::Memcmp {
                left,
                right,
                length,
            } => {
                if tag.is_propagated_by(exp_tag_prop) {
                    left.make_absence_check(tag)
                        .and(right.make_absence_check(tag))
                        .and(length.make_absence_check(tag))
                } else {
                    Rc::new(TRUE)
                }
            }

            Expression::UninterpretedCall {
                callee, arguments, ..
            } => {
                if tag.is_propagated_by(exp_tag_prop) {
                    let mut check = callee.make_absence_check(tag);
                    for argument in arguments {
                        check = check.and(argument.make_absence_check(tag))
                    }
                    check
                } else {
                    Rc::new(TRUE)
                }
            }

            _ => {
                verify_unreachable!();
            }
        }
    }

    /// Creates an abstract value from the given expression and size.
    /// Initializes the optional domains to None.
    #[logfn_inputs(TRACE)]
    pub fn make_from(expression: Expression, expression_size: u64) -> Rc<AbstractValue> {
        if expression_size > k_limits::MAX_EXPRESSION_SIZE {
            if expression_size < u64::MAX {
                trace!("expression {:?}", expression);
                debug!("expression abstracted");
            }
            // If the expression gets too large, refining it gets expensive and composing it
            // into other expressions leads to exponential growth. We therefore need to abstract
            // (go up in the lattice). We do that by making the expression a typed variable and
            // by eagerly computing and caching any other domains, such as the interval domain.
            let var_type = expression.infer_type();
            let val = Rc::new(AbstractValue {
                expression_size,
                ..make_value(expression)
            });
            let interval = val.get_cached_interval();
            let tags = val.get_cached_tags();
            Rc::new(AbstractValue {
                expression: Expression::Variable {
                    path: Path::new_computed(TOP.into()),
                    var_type,
                },
                expression_size: 1,
                interval: RefCell::new(Some(interval)),
                is_non_null: RefCell::new(Some(val.is_non_null())),
                tags: RefCell::new(Some(tags)),
            })
        } else {
            Rc::new(AbstractValue {
                expression_size,
                ..make_value(expression)
            })
        }
    }

    /// Creates an abstract value that is a reference to the memory named by the given path.
    #[logfn_inputs(TRACE)]
    pub fn make_reference(path: Rc<Path>) -> Rc<AbstractValue> {
        if let PathEnum::Offset { value } = &path.value {
            return value.clone();
        }
        let path_length = path.path_length() as u64;
        AbstractValue::make_from(Expression::Reference(path), path_length)
    }

    /// Creates an abstract value about which nothing is known other than its type and address.
    #[logfn_inputs(TRACE)]
    pub fn make_typed_unknown(var_type: ExpressionType, path: Rc<Path>) -> Rc<AbstractValue> {
        let path = path.remove_initial_value_wrapper();
        Rc::new(make_value(Expression::Variable { path, var_type }))
    }

    /// Creates an abstract value about which nothing is known other than its type, address and that
    /// it is rooted in a parameter. This is used to refer to the value of a parameter as it was
    /// before any assignments to it. When transferred into a calling context, this value must be
    /// refined with the environment as it was at the start of the call.
    #[logfn_inputs(TRACE)]
    pub fn make_initial_parameter_value(
        var_type: ExpressionType,
        path: Rc<Path>,
    ) -> Rc<AbstractValue> {
        Rc::new(make_value(Expression::InitialParameterValue {
            path: path.remove_initial_value_wrapper(),
            var_type,
        }))
    }

    /// Creates an abstract value which represents the result of comparing the left operand with
    /// the right operand, according to the rules of memcmp in unix.
    #[logfn_inputs(TRACE)]
    pub fn make_memcmp(
        left: Rc<AbstractValue>,
        right: Rc<AbstractValue>,
        length: Rc<AbstractValue>,
    ) -> Rc<AbstractValue> {
        let expression_size = length
            .expression_size
            .saturating_add(left.expression_size)
            .saturating_add(right.expression_size);
        AbstractValue::make_from(
            Expression::Memcmp {
                left,
                right,
                length,
            },
            expression_size,
        )
    }
}

pub trait AbstractValueTrait: Sized {
    fn addition(&self, other: Self) -> Self;
    fn add_overflows(&self, other: Self, target_type: ExpressionType) -> Self;
    fn add_tag(&self, tag: Tag) -> Self;
    fn and(&self, other: Self) -> Self;
    fn trim_prefix_conjuncts(&self, target_size: u64) -> Option<Self>;
    fn as_bool_if_known(&self) -> Option<bool>;
    fn as_int_if_known(&self) -> Option<Self>;
    fn bit_and(&self, other: Self) -> Self;
    fn bit_not(&self, target_type: ExpressionType) -> Self;
    fn bit_or(&self, other: Self) -> Self;
    fn bit_xor(&self, other: Self) -> Self;
    fn cast(&self, target_type: ExpressionType) -> Self;
    fn conditional_expression(&self, consequent: Self, alternate: Self) -> Self;
    fn dereference(&self, target_type: ExpressionType) -> Self;
    fn divide(&self, other: Self) -> Self;
    fn does_not_have_tag(&self, tag: &Tag) -> Self;
    fn equals(&self, other: Self) -> Self;
    fn extract_promotable_conjuncts(&self, is_post_condition: bool) -> Option<Self>;
    fn extract_promotable_disjuncts(&self, is_post_condition: bool) -> Option<Self>;
    fn greater_or_equal(&self, other: Self) -> Self;
    fn greater_than(&self, other: Self) -> Self;
    fn has_tag(&self, tag: &Tag) -> Rc<AbstractValue>;
    fn implies(&self, other: &Self) -> bool;
    fn implies_not(&self, other: &Self) -> bool;
    fn intrinsic_binary(&self, other: Self, name: KnownNames) -> Self;
    fn intrinsic_bit_vector_unary(&self, bit_length: u8, name: KnownNames) -> Self;
    fn intrinsic_floating_point_unary(&self, name: KnownNames) -> Self;
    fn inverse_implies(&self, other: &Rc<AbstractValue>) -> bool;
    fn inverse_implies_not(&self, other: &Rc<AbstractValue>) -> bool;
    fn is_bottom(&self) -> bool;
    fn is_compile_time_constant(&self) -> bool;
    fn is_contained_in_zeroed_heap_block(&self) -> bool;
    fn is_function(&self) -> bool;
    fn is_non_null(&self) -> bool;
    fn is_top(&self) -> bool;
    fn is_unit(&self) -> bool;
    fn is_zero(&self) -> bool;
    fn join(&self, other: Self) -> Self;
    fn less_or_equal(&self, other: Self) -> Self;
    fn less_than(&self, other: Self) -> Self;
    fn multiply(&self, other: Self) -> Self;
    fn mul_overflows(&self, other: Self, target_type: ExpressionType) -> Self;
    fn negate(&self) -> Self;
    fn not_equals(&self, other: Self) -> Self;
    fn logical_not(&self) -> Self;
    fn offset(&self, other: Self) -> Self;
    fn or(&self, other: Self) -> Self;
    fn record_heap_blocks_and_strings(&self, result: &mut HashSet<Rc<AbstractValue>>);
    fn remainder(&self, other: Self) -> Self;
    fn remove_conjuncts_that_depend_on(&self, variables: &HashSet<Rc<Path>>) -> Self;
    fn shift_left(&self, other: Self) -> Self;
    fn shl_overflows(&self, other: Self, target_type: ExpressionType) -> Self;
    fn shr(&self, other: Self) -> Self;
    fn shr_overflows(&self, other: Self, target_type: ExpressionType) -> Self;
    fn subtract(&self, other: Self) -> Self;
    fn sub_overflows(&self, other: Self, target_type: ExpressionType) -> Self;
    fn subset(&self, other: &Self) -> bool;
    fn switch(
        &self,
        cases: Vec<(Rc<AbstractValue>, Rc<AbstractValue>)>,
        default: Rc<AbstractValue>,
    ) -> Rc<AbstractValue>;
    fn try_to_retype_as(&self, target_type: ExpressionType) -> Self;
    fn try_to_constant_fold_and_distribute_binary_op(
        &self,
        other: Self,
        const_op: fn(&ConstantDomain, &ConstantDomain) -> ConstantDomain,
        recursive_op: fn(&Self, Self) -> Self,
        operation: fn(Self, Self) -> Self,
    ) -> Self;
    fn try_to_constant_fold_and_distribute_typed_binary_op(
        &self,
        other: Self,
        target_type: ExpressionType,
        const_op: fn(&ConstantDomain, &ConstantDomain, ExpressionType) -> ConstantDomain,
        recursive_op: fn(&Self, Self, ExpressionType) -> Self,
        operation: fn(Self, Self, ExpressionType) -> Self,
    ) -> Self;
    fn try_to_constant_fold_and_distribute_typed_unary_op(
        &self,
        target_type: ExpressionType,
        const_op: fn(&ConstantDomain, ExpressionType) -> ConstantDomain,
        recursive_op: fn(&Self, ExpressionType) -> Self,
        operation: fn(Self, ExpressionType) -> Self,
    ) -> Self;
    fn try_to_constant_fold_and_distribute_unary_op(
        &self,
        const_op: fn(&ConstantDomain) -> ConstantDomain,
        recursive_op: fn(&Self) -> Self,
        operation: fn(Self) -> Self,
    ) -> Self;
    fn try_to_distribute_binary_op(
        &self,
        other: Self,
        recursive_op: fn(&Self, Self) -> Self,
        operation: fn(Self, Self) -> Self,
    ) -> Self;
    fn try_to_distribute_typed_binary_op(
        &self,
        other: Self,
        target_type: ExpressionType,
        recursive_op: fn(&Self, Self, ExpressionType) -> Self,
        operation: fn(Self, Self, ExpressionType) -> Self,
    ) -> Self;
    fn try_to_distribute_typed_unary_op(
        &self,
        target_type: ExpressionType,
        recursive_op: fn(&Self, ExpressionType) -> Self,
        operation: fn(Self, ExpressionType) -> Self,
    ) -> Self;
    fn try_to_distribute_unary_op(
        &self,
        recursive_op: fn(&Self) -> Self,
        operation: fn(Self) -> Self,
    ) -> Self;
    fn get_cached_interval(&self) -> Rc<IntervalDomain>;
    fn get_as_interval(&self) -> IntervalDomain;
    fn get_is_non_null(&self) -> bool;
    fn get_cached_tags(&self) -> Rc<TagDomain>;
    fn get_tags(&self) -> TagDomain;
    fn get_widened_subexpression(&self, path: &Rc<Path>) -> Option<Rc<AbstractValue>>;
    fn refine_parameters_and_paths(
        &self,
        args: &[(Rc<Path>, Rc<AbstractValue>)],
        result: &Option<Rc<Path>>,
        pre_env: &Environment,
        post_env: &Environment,
        fresh: usize,
    ) -> Self;
    fn refine_with(&self, path_condition: &Self, depth: usize) -> Self;
    fn replace_embedded_path_root(&self, old_root: &Rc<Path>, new_root: Rc<Path>) -> Self;
    fn transmute(&self, target_type: ExpressionType) -> Self;
    fn try_resolve_as_byte_array(&self, _environment: &Environment) -> Option<Vec<u8>>;
    fn try_resolve_as_ref_to_str(&self, environment: &Environment) -> Option<Rc<str>>;
    fn uninterpreted_call(
        &self,
        arguments: Vec<Rc<AbstractValue>>,
        result_type: ExpressionType,
        path: Rc<Path>,
    ) -> Self;
    fn unsigned_modulo(&self, num_bits: u8) -> Self;
    fn unsigned_shift_left(&self, num_bits: u8) -> Self;
    fn unsigned_shift_right(&self, num_bits: u8) -> Self;
    fn uses(&self, variables: &HashSet<Rc<Path>>) -> bool;
    fn widen(&self, path: &Rc<Path>) -> Self;
}

impl AbstractValueTrait for Rc<AbstractValue> {
    /// Returns an element that is "self + other".
    #[logfn_inputs(TRACE)]
    fn addition(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        // [x + c] -> c + x
        if !self.is_compile_time_constant() && other.is_compile_time_constant() {
            // Normalize binary expressions so that if only one of the operands is a constant, it is
            // always the left operand.
            return other.addition(self.clone());
        }
        if let Expression::CompileTimeConstant(c1) = &self.expression {
            // [0 + x] -> x
            if c1.is_zero() {
                return other;
            }
            // [c1 + (c2 + x)] -> c3 + x where c3 = c1 + c2
            if let Expression::Add { left, right: x } = &other.expression {
                if let Expression::CompileTimeConstant(c2) = &left.expression {
                    let c3 = c1.add(c2);
                    if c3 != ConstantDomain::Bottom {
                        let c3val: Rc<AbstractValue> = Rc::new(c3.into());
                        return c3val.addition(x.clone());
                    }
                }
            }
        }

        // [x + (-y)] -> x - y
        if let Expression::Neg { operand } = &other.expression {
            return self.subtract(operand.clone());
        }
        // [(-x) + y] -> y - x
        if let Expression::Neg { operand } = &self.expression {
            return other.subtract(operand.clone());
        }
        // [x + x] -> 2 * x
        if self.eq(&other) {
            let t = self.expression.infer_type();
            if t.is_unsigned_integer() {
                let two: Rc<AbstractValue> = Rc::new(ConstantDomain::U128(2).into());
                return two.multiply(other);
            } else if t.is_signed_integer() {
                let two: Rc<AbstractValue> = Rc::new(ConstantDomain::I128(2).into());
                return two.multiply(other);
            }
        }

        // [x + (y - x)] -> y
        if let Expression::Sub { left: y, right: x } = &other.expression {
            if self.eq(x) {
                return y.clone();
            }
        }

        // [(c * x) + (c * y)] -> c * (x + y)
        if let (
            Expression::Mul {
                left: cv1,
                right: x,
            },
            Expression::Mul {
                left: cv2,
                right: y,
            },
        ) = (&self.expression, &other.expression)
        {
            if let (Expression::CompileTimeConstant(c1), Expression::CompileTimeConstant(c2)) =
                (&cv1.expression, &cv2.expression)
            {
                if !c1.eq(c2) {
                    let right = x.addition(y.clone());
                    // Don't use multiply because we don't want to simplify this
                    let expression_size = cv1
                        .expression_size
                        .saturating_add(right.expression_size)
                        .saturating_add(1);
                    return AbstractValue::make_from(
                        Expression::Mul {
                            left: cv1.clone(),
                            right,
                        },
                        expression_size,
                    );
                }
            }
        }

        self.try_to_constant_fold_and_distribute_binary_op(
            other,
            ConstantDomain::add,
            Self::addition,
            |l, r| AbstractValue::make_binary(l, r, |left, right| Expression::Add { left, right }),
        )
    }

    /// Returns an element that is true if "self + other" is not in range of target_type.
    #[logfn_inputs(TRACE)]
    fn add_overflows(
        &self,
        other: Rc<AbstractValue>,
        target_type: ExpressionType,
    ) -> Rc<AbstractValue> {
        // [x + c] -> c + x
        if !self.is_compile_time_constant() && other.is_compile_time_constant() {
            // Normalize binary expressions so that if only one of the operands is a constant, it is
            // always the left operand.
            return other.add_overflows(self.clone(), target_type);
        }
        if self.is_bottom() || self.is_top() || other.is_bottom() || other.is_top() {
            return AbstractValue::make_typed_unknown(
                ExpressionType::Bool,
                Path::new_computed(TOP.into()),
            );
        }
        if let Expression::CompileTimeConstant(c1) = &self.expression {
            // [0 + x] -> x
            if c1.is_zero() {
                return Rc::new(FALSE);
            }
            // [c1 + (c2 + x)] -> c3 + x where c3 = c1 + c2
            if let Expression::Add { left, right: x } = &other.expression {
                if let Expression::CompileTimeConstant(c2) = &left.expression {
                    let c3 = c1.add(c2);
                    if c3 != ConstantDomain::Bottom {
                        let c3val: Rc<AbstractValue> = Rc::new(c3.into());
                        return c3val.add_overflows(x.clone(), target_type);
                    }
                }
            }
        }
        // [x + x] -> 2 * x
        if self.eq(&other) {
            let t = self.expression.infer_type();
            if t.is_unsigned_integer() {
                let two: Rc<AbstractValue> = Rc::new(ConstantDomain::U128(2).into());
                return two.mul_overflows(other, target_type);
            } else if t.is_signed_integer() {
                let two: Rc<AbstractValue> = Rc::new(ConstantDomain::I128(2).into());
                return two.mul_overflows(other, target_type);
            }
        }

        let interval = self.get_cached_interval().add(&other.get_cached_interval());
        if interval.is_contained_in(target_type) {
            return Rc::new(FALSE);
        }
        self.try_to_constant_fold_and_distribute_typed_binary_op(
            other,
            target_type,
            ConstantDomain::add_overflows,
            Self::add_overflows,
            |l, r, t| {
                AbstractValue::make_typed_binary(l, r, t, |left, right, result_type| {
                    Expression::AddOverflows {
                        left,
                        right,
                        result_type,
                    }
                })
            },
        )
    }

    /// Returns an element that is `self` attached with `tag`.
    #[logfn_inputs(TRACE)]
    fn add_tag(&self, tag: Tag) -> Rc<AbstractValue> {
        if self.is_bottom()
            || self.is_top()
            || self.get_cached_tags().has_tag(&tag) == BoolDomain::True
        {
            self.clone()
        } else {
            AbstractValue::make_from(
                Expression::TaggedExpression {
                    operand: self.clone(),
                    tag,
                },
                self.expression_size.saturating_add(1),
            )
        }
    }

    /// Returns an element that is "self && other".
    #[logfn_inputs(TRACE)]
    fn and(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        fn is_contained_in(x: &Rc<AbstractValue>, y: &Rc<AbstractValue>) -> bool {
            if x.eq(y) {
                return true;
            }
            if let Expression::And { left, right } = &y.expression {
                is_contained_in(x, left) || is_contained_in(x, right)
            } else {
                false
            }
        }

        // Do these tests here lest BOTTOM get simplified away.
        if self.is_bottom() || other.is_top() {
            return self.clone();
        }
        if other.is_bottom() || self.is_top() {
            return other;
        }
        let self_bool = self.as_bool_if_known();
        if let Some(false) = self_bool {
            // [false && other] -> false
            return Rc::new(FALSE);
        };
        let other_bool = other.as_bool_if_known();
        if let Some(false) = other_bool {
            // [self && false] -> false
            return Rc::new(FALSE);
        };
        if self_bool.unwrap_or(false) {
            if other_bool.unwrap_or(false) {
                // [true && true] -> true
                Rc::new(TRUE)
            } else {
                // [true && other] -> other
                other
            }
        } else if other_bool.unwrap_or(false) {
            // [self && true] -> self
            self.clone()
        } else {
            // [x && (x && y)] -> x && y
            // [y && (x && y)] -> x && y
            // [(x && y) && x] -> x && y
            // [(x && y) && y] -> x && y
            if is_contained_in(self, &other) {
                return other;
            } else if is_contained_in(&other, self) {
                return self.clone();
            }
            match &self.expression {
                Expression::And { left: x, right: yz } => {
                    if let Expression::Or { left: y, right: z } = &yz.expression {
                        // [(x && (y || z)) && z] -> x && z
                        // [(x && (y || z)) && y] -> x && y
                        if y.eq(&other) || z.eq(&other) {
                            return x.and(other);
                        }
                        // [(x && (y || z)) && !a] -> (x && z) && !a if y => a
                        if let Expression::LogicalNot { operand: y2 } = &other.expression {
                            if y.implies(y2) {
                                return x.and(z.clone()).and(other);
                            }
                        }
                    }
                    // [(x && !y) && y] -> false
                    if let Expression::LogicalNot { operand: y } = &yz.expression {
                        if y.eq(&other) {
                            return Rc::new(FALSE);
                        }
                    }
                }
                Expression::LogicalNot { operand } if operand.eq(&other) => {
                    // [!x && x] -> false
                    return Rc::new(FALSE);
                }
                Expression::Or { left: x, right: y } => {
                    // [((c == x) || y) && (c != x)] -> y
                    if let (
                        Expression::Equals {
                            left: c1,
                            right: x1,
                        },
                        Expression::Ne {
                            left: c2,
                            right: x2,
                        },
                    ) = (&x.expression, &other.expression)
                    {
                        if c1.eq(c2) && x1.eq(x2) {
                            return y.clone();
                        }
                    }

                    // [(x || (c == y)) && (c != y)] -> x
                    if let (
                        Expression::Equals {
                            left: c1,
                            right: x1,
                        },
                        Expression::Ne {
                            left: c2,
                            right: x2,
                        },
                    ) = (&y.expression, &other.expression)
                    {
                        if c1.eq(c2) && x1.eq(x2) {
                            return x.clone();
                        }
                    }

                    // [(x || y) && x] -> x
                    // [(x || y) && y] -> y
                    if other.implies(x) || other.implies(y) {
                        return other;
                    }
                    if let Expression::LogicalNot { operand } = &other.expression {
                        // [(x || y) && (!x)] -> y && !x
                        if x.eq(operand) {
                            return y.and(other);
                        }
                        // [(x || y) && (!y)] -> x && !y
                        if y.eq(operand) {
                            return x.and(other);
                        }
                    }
                }
                _ => (),
            }
            match &other.expression {
                Expression::And { left: x, right: y } => {
                    // [x && (x && y)] -> x && y
                    // [y && (x && y)] -> x && y
                    if x.eq(self) || y.eq(self) {
                        return other.clone();
                    }
                }
                // [x && c == y] -> c == y if refining x with c == y produces true
                Expression::Equals { left: c, .. }
                    if self.expression_size < k_limits::MAX_EXPRESSION_SIZE / 10
                        && c.is_compile_time_constant()
                        && self
                            .refine_with(&other, 35)
                            .as_bool_if_known()
                            .unwrap_or(false) =>
                {
                    return other.clone();
                }
                // [x && (true join x)] -> x
                Expression::Join { left, right: x }
                    if left.as_bool_if_known().unwrap_or(false) && self.eq(x) =>
                {
                    return self.clone();
                }
                // [x && (x join true)] -> x
                Expression::Join { left: x, right }
                    if right.as_bool_if_known().unwrap_or(false) && self.eq(x) =>
                {
                    return self.clone();
                }
                // [x && (true join false)] -> x
                Expression::Join { left: x, right: y }
                    if x.as_bool_if_known().unwrap_or(false)
                        && !y.as_bool_if_known().unwrap_or(true) =>
                {
                    return self.clone();
                }
                // [x && (false join true)] -> x
                Expression::Join { left: x, right: y }
                    if !x.as_bool_if_known().unwrap_or(true)
                        && y.as_bool_if_known().unwrap_or(false) =>
                {
                    return self.clone();
                }
                Expression::LogicalNot { operand } if operand.eq(self) => {
                    // [x && !x] -> false
                    return Rc::new(FALSE);
                }
                Expression::Or { left: x, right: y } => {
                    // [x && (x || y)] -> x
                    // [y && (x || y)] -> y
                    if x.eq(self) || y.eq(self) {
                        return self.clone();
                    }
                    if let Expression::LogicalNot { operand } = &self.expression {
                        // [(!x) && (x || y)] -> !x && y
                        if x.eq(operand) {
                            return self.and(y.clone());
                        }
                        // [(!y) && (x || y) ] -> !y && x
                        if y.eq(operand) {
                            return self.and(x.clone());
                        }
                    }
                    // [x && (x && y || x && z)] -> x && (y || z)
                    if let (
                        Expression::And { left: x1, right: y },
                        Expression::And { left: x2, right: z },
                    ) = (&x.expression, &y.expression)
                    {
                        if self.eq(x1) && self.eq(x2) {
                            return self.and(y.or(z.clone()));
                        }
                    }
                }
                _ => (),
            }
            match (&self.expression, &other.expression) {
                // [(a && (b != x)) && (c < x)] -> a && (c < x) if c >= b
                (
                    Expression::And {
                        left: a1,
                        right: bx,
                    },
                    Expression::LessThan { left: c, right: x2 },
                ) => {
                    if let Expression::Ne { left: b, right: x1 } = &bx.expression {
                        if x1.eq(x2)
                            && c.greater_or_equal(b.clone())
                                .as_bool_if_known()
                                .unwrap_or(false)
                        {
                            return a1.and(other);
                        }
                    }
                }

                // [(a && (x || b)) && (a && b)] -> a && b
                // [(a && (0 == x)) && (x && b)] -> false
                (
                    Expression::And {
                        left: a1,
                        right: xb,
                    },
                    Expression::And {
                        left: a2,
                        right: b2,
                    },
                ) => {
                    if let Expression::Or { right: b1, .. } = &xb.expression {
                        if a1.eq(a2) && b1.eq(b2) {
                            return other.clone();
                        }
                    }
                    if let Expression::Equals { left, right: x } = &xb.expression {
                        if left.is_zero() && x.eq(a2) {
                            return Rc::new(FALSE);
                        }
                    }
                }
                // [(a && (b || x )) && (x || y)] -> a && (x || (b && y)
                (Expression::And { left: a, right: bx }, Expression::Or { left: x2, right: y }) => {
                    if let Expression::Or { left: b, right: x1 } = &bx.expression {
                        if x1.eq(x2) {
                            return a.and(x1.or(b.and(y.clone())));
                        }
                    }
                }
                // [(c ? a : b) && (c ? x : y)] -> c ? (a && x) : (b && y)
                (
                    Expression::ConditionalExpression {
                        condition: c,
                        consequent: a,
                        alternate: b,
                    },
                    ConditionalExpression {
                        condition,
                        consequent,
                        alternate,
                    },
                ) if c.eq(condition) => {
                    return c.conditional_expression(
                        a.and(consequent.clone()),
                        b.and(alternate.clone()),
                    );
                }

                // [!x && !y] -> !(x || y)
                (Expression::LogicalNot { operand: x }, Expression::LogicalNot { operand: y }) => {
                    return x.or(y.clone()).logical_not();
                }
                // [!(x && y) && x] -> x
                // [!(x && y) && y] -> y
                (Expression::LogicalNot { operand }, _) => {
                    if let Expression::And { left: x, right: y } = &operand.expression {
                        if x.eq(&other) || y.eq(&other) {
                            return other;
                        }
                    }
                }

                // [(x || y) && (!y && z)] -> x && !y && z
                (Expression::Or { left: x, right: y1 }, Expression::And { left: ny, right: z }) => {
                    if let Expression::LogicalNot { operand: y2 } = &ny.expression {
                        if y1.eq(y2) {
                            return x.and(ny.and(z.clone()));
                        }
                    }
                }
                // [(x || !y) && !(x || y)] -> !x && !y
                (
                    Expression::Or {
                        left: x1,
                        right: ny,
                    },
                    Expression::LogicalNot { operand: xy },
                ) if matches!(xy.expression, Expression::Or { .. }) => {
                    if let Expression::LogicalNot { operand: y1 } = &ny.expression {
                        if let Expression::Or {
                            left: x2,
                            right: y2,
                        } = &xy.expression
                        {
                            if x1.eq(x2) && y1.eq(y2) {
                                return x1.logical_not().and(ny.clone());
                            }
                        }
                    }
                }
                (
                    Expression::Or {
                        left: x1,
                        right: yz,
                    },
                    y,
                ) => {
                    // [(x || (y && z)) && y] -> [(x && y) || (y && z && y)] -> (x && y) || (y && z)
                    if let Expression::And { left: y1, right: z } = &yz.expression {
                        if y1.eq(&other) {
                            return x1.and(y1.clone()).or(y1.and(z.clone()));
                        }
                    }
                    if let Expression::Or {
                        left: x2,
                        right: y2,
                    } = y
                    {
                        // [(x || !y) && (x || y)] -> x
                        if let Expression::LogicalNot { operand: y1 } = &yz.expression {
                            if x1.eq(x2) && y1.eq(y2) {
                                return x1.clone();
                            }
                        }
                        // [(x || y) && (x || !y)] -> x
                        if let Expression::LogicalNot { operand: y2a } = &y2.expression {
                            if x1.eq(x2) && yz.eq(y2a) {
                                return x1.clone();
                            }
                        }
                    }
                    // [(0 = x || k == x) && (0 != x)] -> k == x if k != 0
                    if let Expression::Ne { left: c, right: x3 } = y {
                        if c.is_zero() {
                            if let (
                                Expression::Equals { left: e, right: x1 },
                                Expression::Equals { left: k, right: x2 },
                            ) = (&x1.expression, &yz.expression)
                            {
                                if x1.eq(x2)
                                    && x2.eq(x3)
                                    && e.is_zero()
                                    && k.is_compile_time_constant()
                                    && !k.is_zero()
                                {
                                    return yz.clone();
                                }
                            }
                        }
                    }
                }
                // [(x >= y) && (x == y)] -> x == y
                // [(x >= y) && (x > y)] -> x > y
                (
                    Expression::GreaterOrEqual {
                        left: x1,
                        right: y1,
                    },
                    Expression::Equals {
                        left: x2,
                        right: y2,
                    }
                    | Expression::GreaterThan {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2) && y1.eq(y2) => {
                    return other.clone();
                }
                // [(x <= y) && (x == y)] -> x == y
                // [(x <= y) && (x < y)] -> x < y
                (
                    Expression::LessOrEqual {
                        left: x1,
                        right: y1,
                    },
                    Expression::Equals {
                        left: x2,
                        right: y2,
                    }
                    | Expression::LessThan {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2) && y1.eq(y2) => {
                    return other.clone();
                }
                // [(x == y) && (x >= y)] -> x == y
                // [(x > y) && (x >= y)] -> x > y
                (
                    Expression::Equals {
                        left: x1,
                        right: y1,
                    }
                    | Expression::GreaterThan {
                        left: x1,
                        right: y1,
                    },
                    Expression::GreaterOrEqual {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2) && y1.eq(y2) => {
                    return self.clone();
                }
                // [(x == y) && (x <= y)] -> x == y
                // [(x < y) && (x <= y)] -> x < y
                (
                    Expression::Equals {
                        left: x1,
                        right: y1,
                    }
                    | Expression::LessThan {
                        left: x1,
                        right: y1,
                    },
                    Expression::LessOrEqual {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2) && y1.eq(y2) => {
                    return self.clone();
                }
                // [(x >= y) && (x != y)] -> x > y
                (
                    Expression::GreaterOrEqual {
                        left: x1,
                        right: y1,
                    },
                    Expression::Ne {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2) && y1.eq(y2) => {
                    return x1.greater_than(y1.clone());
                }
                // [(x <= y) && (x != y)] -> x < y
                (
                    Expression::LessOrEqual {
                        left: x1,
                        right: y1,
                    },
                    Expression::Ne {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2) && y1.eq(y2) => {
                    return x1.less_than(y1.clone());
                }
                // [(x <= y) && (x < z)] -> x < z if z <= y
                (
                    Expression::LessOrEqual { left: x1, right: y },
                    Expression::LessThan { left: x2, right: z },
                ) if x1.eq(x2) => {
                    if let (
                        Expression::CompileTimeConstant(c1),
                        Expression::CompileTimeConstant(c2),
                    ) = (&y.expression, &z.expression)
                    {
                        if c2.less_or_equal(c1).is_true() {
                            return other.clone();
                        }
                    }
                }
                // [(x != y) && (x >= y)] -> x > y
                (
                    Expression::Ne {
                        left: x1,
                        right: y1,
                    },
                    Expression::GreaterOrEqual {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2) && y1.eq(y2) => {
                    return x1.greater_than(y1.clone());
                }
                // [(x != y) && (x <= y)] -> x < y
                (
                    Expression::Ne {
                        left: x1,
                        right: y1,
                    },
                    Expression::LessOrEqual {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2) && y1.eq(y2) => {
                    return x1.less_than(y1.clone());
                }
                // [(x <= y) && (x >= y)] -> x == y
                (
                    Expression::LessOrEqual {
                        left: x1,
                        right: y1,
                    },
                    Expression::GreaterOrEqual {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2) && y1.eq(y2) => {
                    return x1.equals(y1.clone());
                }
                // [(x && (y >= z)) && (z != y)] -> x && (y > z)
                (
                    Expression::And { left: x, right: yz },
                    Expression::Ne {
                        left: z1,
                        right: y1,
                    },
                ) => {
                    if let Expression::GreaterOrEqual {
                        left: y2,
                        right: z2,
                    } = &yz.expression
                    {
                        if y1.eq(y2) && z1.eq(z2) {
                            return x.and(y1.greater_than(z1.clone()));
                        }
                    }
                }
                _ => (),
            }

            // Refine other expression, except if it is known, or it is an assumed condition
            // (the latter having an expression size zero so that they get retained when
            // conjuncts are pruned away because of an expression overflow).
            let other = if self_bool.is_none()
                && other.expression_size > 0
                && other.expression_size < k_limits::MAX_EXPRESSION_SIZE / 10
            {
                other.refine_with(self, 35)
            } else {
                other
            };
            if let Some(false) = other.as_bool_if_known() {
                return other;
            }
            if other.expression_size >= k_limits::MAX_EXPRESSION_SIZE {
                return other;
            }
            let mut trimmed_self = self.clone();
            if self.expression_size.saturating_add(other.expression_size)
                > k_limits::MAX_EXPRESSION_SIZE
            {
                // The overall expression is going to overflow, so abstract away part of the self
                // (left) expression to keep the overall expression within bounds.
                // We keep the right expression intact because it is usually path conditions that
                // overflow and in a path condition the most recent (i.e. the right hand) condition
                // is the most useful. In particular, we don't want to abstract away assume conditions.
                if let Some(trimmed) = self
                    .trim_prefix_conjuncts(k_limits::MAX_EXPRESSION_SIZE - other.expression_size)
                {
                    debug!("and expression prefix trimmed, self: {:?}", self);
                    trimmed_self = trimmed;
                } else {
                    return other;
                }
            }
            AbstractValue::make_binary(trimmed_self, other, |left, right| Expression::And {
                left,
                right,
            })
        }
    }

    /// Returns an value with an expression that is either TOP or TOP && something, but with
    /// the other domains precomputed from the original expression.
    /// This helps path conditions to stay within limits while losing as little information as possible.
    /// The returned expression must be of size at most target_size.
    #[logfn_inputs(TRACE)]
    fn trim_prefix_conjuncts(&self, target_size: u64) -> Option<Rc<AbstractValue>> {
        precondition!(target_size > 0);
        if let Expression::And { left, right } = &self.expression {
            if right.expression_size < target_size - 1 {
                if let Some(trimmed_left) =
                    left.trim_prefix_conjuncts(target_size - right.expression_size)
                {
                    Some(trimmed_left.and(right.clone()))
                } else {
                    Some(right.clone())
                }
            } else {
                right.trim_prefix_conjuncts(target_size)
            }
        } else {
            None
        }
    }

    /// The Boolean value of this expression, if known, otherwise None.
    #[logfn_inputs(TRACE)]
    fn as_bool_if_known(&self) -> Option<bool> {
        match self.expression {
            Expression::CompileTimeConstant(ConstantDomain::True) => Some(true),
            Expression::CompileTimeConstant(ConstantDomain::False) => Some(false),
            _ => None,
        }
    }

    /// If the concrete Boolean value of this abstract value is known, return it as a UI28 constant,
    /// otherwise return None.
    #[logfn_inputs(TRACE)]
    fn as_int_if_known(&self) -> Option<Rc<AbstractValue>> {
        self.as_bool_if_known()
            .map(|b| Rc::new(ConstantDomain::U128(b as u128).into()))
    }

    /// Returns an element that is "self & other".
    #[logfn_inputs(TRACE)]
    fn bit_and(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        // [x & c] -> c & x
        if !self.is_compile_time_constant() && other.is_compile_time_constant() {
            // Normalize binary expressions so that if only one of the operands is a constant, it is
            // always the left operand.
            return other.bit_and(self.clone());
        }
        let self_bool = self.as_bool_if_known();
        if let Some(false) = self_bool {
            // [false & y] -> false
            return Rc::new(FALSE);
        };
        let other_bool = other.as_bool_if_known();
        if let Some(false) = other_bool {
            // [x & false] -> false
            return Rc::new(FALSE);
        };
        if let Expression::CompileTimeConstant(ConstantDomain::I128(0))
        | Expression::CompileTimeConstant(ConstantDomain::U128(0)) = self.expression
        {
            // [0 & y] -> 0
            return self.clone();
        }
        if let Expression::CompileTimeConstant(ConstantDomain::I128(0))
        | Expression::CompileTimeConstant(ConstantDomain::U128(0)) = other.expression
        {
            // [x & 0] -> 0
            return other.clone();
        }
        // [x & x] -> x
        if self.eq(&other) {
            return other;
        }
        self.try_to_constant_fold_and_distribute_binary_op(
            other,
            ConstantDomain::bit_and,
            Self::bit_and,
            |l, r| {
                AbstractValue::make_binary(l, r, |left, right| Expression::BitAnd { left, right })
            },
        )
    }

    /// Returns an element that is "!self" where self is an integer.
    #[logfn_inputs(TRACE)]
    fn bit_not(&self, result_type: ExpressionType) -> Rc<AbstractValue> {
        self.try_to_constant_fold_and_distribute_typed_unary_op(
            result_type,
            ConstantDomain::bit_not,
            Self::bit_not,
            |o, t| {
                AbstractValue::make_typed_unary(o, t, |operand, result_type| Expression::BitNot {
                    operand,
                    result_type,
                })
            },
        )
    }

    /// Returns an element that is "self | other".
    #[logfn_inputs(TRACE)]
    fn bit_or(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        // [x | c] -> c | x
        if !self.is_compile_time_constant() && other.is_compile_time_constant() {
            // Normalize binary expressions so that if only one of the operands is a constant, it is
            // always the left operand.
            return other.bit_or(self.clone());
        }
        if let Expression::CompileTimeConstant(ConstantDomain::I128(0))
        | Expression::CompileTimeConstant(ConstantDomain::U128(0)) = self.expression
        {
            // [0 | y] -> y
            return other;
        }
        if let Expression::CompileTimeConstant(ConstantDomain::I128(0))
        | Expression::CompileTimeConstant(ConstantDomain::U128(0)) = other.expression
        {
            // [x | 0] -> x
            return self.clone();
        }
        // [x | x] -> x
        if self.eq(&other) {
            return other;
        }
        self.try_to_constant_fold_and_distribute_binary_op(
            other,
            ConstantDomain::bit_or,
            Self::bit_or,
            |l, r| {
                AbstractValue::make_binary(l, r, |left, right| Expression::BitOr { left, right })
            },
        )
    }

    /// Returns an element that is "self ^ other".
    #[logfn_inputs(TRACE)]
    fn bit_xor(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        // [x ^ c] -> c ^ x
        if !self.is_compile_time_constant() && other.is_compile_time_constant() {
            // Normalize binary expressions so that if only one of the operands is a constant, it is
            // always the left operand.
            return other.bit_xor(self.clone());
        }
        if self.eq(&other) {
            return Rc::new(0u128.into());
        }
        self.try_to_constant_fold_and_distribute_binary_op(
            other,
            ConstantDomain::bit_xor,
            Self::bit_xor,
            |l, r| {
                AbstractValue::make_binary(l, r, |left, right| Expression::BitXor { left, right })
            },
        )
    }

    /// Returns an element that is "self as target_type".
    #[logfn_inputs(TRACE)]
    fn cast(&self, target_type: ExpressionType) -> Rc<AbstractValue> {
        match &self.expression {
            Expression::Bottom => self.clone(),
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => condition
                .conditional_expression(consequent.cast(target_type), alternate.cast(target_type)),
            Expression::Join { left, right } => {
                left.cast(target_type).join(right.cast(target_type))
            }
            Expression::Switch {
                discriminator,
                cases,
                default,
            } => discriminator.switch(
                cases
                    .iter()
                    .map(|(case_val, result_val)| (case_val.clone(), result_val.cast(target_type)))
                    .collect(),
                default.cast(target_type),
            ),
            _ => {
                match &self.expression {
                    // [(x as t1) as target_type] -> x as target_type if t1.max_value() >= target_type.max_value()
                    Expression::Cast {
                        operand,
                        target_type: t1,
                    } => {
                        if t1.is_integer()
                            && target_type.is_unsigned_integer()
                            && t1
                                .max_value()
                                .greater_or_equal(&target_type.max_value())
                                .as_bool_if_known()
                                .unwrap_or(false)
                        {
                            return operand.cast(target_type);
                        }
                    }
                    // [(x % c1) as t] -> (x as t) if c1 == t.modulo_value()
                    Expression::Rem { left, right } => {
                        if right
                            .equals(target_type.modulo_value())
                            .as_bool_if_known()
                            .unwrap_or(false)
                        {
                            return left.cast(target_type);
                        }
                    }
                    // [(v : t1) as target_type] -> (v: t1) if t1.max_value() == target_type.max_value()
                    Expression::Variable { var_type: t1, .. }
                    | Expression::InitialParameterValue { var_type: t1, .. } => {
                        if t1.is_integer()
                            && target_type.is_unsigned_integer()
                            && t1
                                .max_value()
                                .equals(&target_type.max_value())
                                .as_bool_if_known()
                                .unwrap_or(false)
                        {
                            return self.clone();
                        }
                    }
                    _ => (),
                }
                let source_type = self.expression.infer_type();
                if source_type != target_type {
                    if source_type == ExpressionType::NonPrimitive
                        && target_type == ExpressionType::ThinPointer
                    {
                        let field0 = Path::new_field(Path::get_as_path(self.clone()), 0);
                        AbstractValue::make_typed_unknown(target_type, field0)
                    } else {
                        self.try_to_constant_fold_and_distribute_typed_unary_op(
                            target_type,
                            ConstantDomain::cast,
                            Self::cast,
                            |o, t| {
                                AbstractValue::make_typed_unary(o, t, |operand, target_type| {
                                    Expression::Cast {
                                        operand,
                                        target_type,
                                    }
                                })
                            },
                        )
                    }
                } else {
                    self.clone()
                }
            }
        }
    }

    /// Returns an element that is "if self { consequent } else { alternate }".
    #[logfn_inputs(TRACE)]
    fn conditional_expression(
        &self,
        mut consequent: Rc<AbstractValue>,
        mut alternate: Rc<AbstractValue>,
    ) -> Rc<AbstractValue> {
        if self.is_bottom() {
            // If the condition is impossible so is the expression.
            return self.clone();
        }
        // If either of the branches is impossible, it must be the other one.
        if consequent.is_bottom() {
            return alternate;
        }
        if alternate.is_bottom() {
            return consequent;
        }
        // If the branches are the same, the condition does no matter.
        if consequent.eq(&alternate) {
            // [c ? x : x] -> x
            return consequent;
        }
        // If the condition is unknown, the rules below won't fire.
        if self.is_top() {
            return self.clone();
        }
        if self.eq(&consequent) {
            // [x ? x : y] -> x || y
            return self.or(alternate);
        }
        if self.eq(&alternate) {
            // [y ? x : y] -> y && x
            return self.and(consequent);
        }
        let self_as_bool = self.as_bool_if_known();
        if self_as_bool == Some(true) {
            // [true ? x : y] -> x
            return consequent;
        } else if self_as_bool == Some(false) {
            // [false ? x : y] -> y
            return alternate;
        }
        // simplification rules are heuristic and can be non symmetric.
        let not_self = self.logical_not();
        let not_self_as_bool = not_self.as_bool_if_known();
        if not_self_as_bool == Some(false) {
            // [true ? x : y] -> x
            return consequent;
        } else if not_self_as_bool == Some(true) {
            // [false ? x : y] -> y
            return alternate;
        }
        if let (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) =
            (&consequent.expression, &alternate.expression)
        {
            match (v1, v2) {
                (ConstantDomain::True, ConstantDomain::False) => {
                    // [c ? true : false] -> c
                    return self.clone();
                }
                (ConstantDomain::False, ConstantDomain::True) => {
                    // [c ? false : true] -> !c
                    return self.logical_not();
                }
                _ => (),
            }
        }
        if let Expression::LogicalNot { operand } = &self.expression {
            // [if !(x) { a } else { b }] -> if x { b } else { a }
            return operand.conditional_expression(alternate, consequent);
        }
        // [if 0 == x { y } else { true }] -> x || y
        // [if 0 == x { false } else { y }] -> x && y
        if let Expression::Equals { left: z, right: x } = &self.expression {
            if let Expression::CompileTimeConstant(ConstantDomain::U128(0)) = z.expression {
                if alternate.as_bool_if_known().unwrap_or(false) {
                    return x.or(consequent);
                }
                if !consequent.as_bool_if_known().unwrap_or(true) {
                    return x.and(alternate);
                }
            }
        }
        // [if 0 != x { x } else { 0 } ] -> x
        // [if 0 != x { 0 } else { x } ] -> x
        if let Expression::Ne { left: z, right: x } = &self.expression {
            if let Expression::CompileTimeConstant(ConstantDomain::U128(0)) = z.expression {
                if consequent.eq(x) {
                    if alternate.is_zero() {
                        return consequent;
                    }
                } else if alternate.eq(x) && consequent.is_zero() {
                    return alternate;
                }
            }
        }
        let consequent_as_bool_if_known = consequent.as_bool_if_known();
        // [if x { true } else { y }] -> x || y
        if consequent_as_bool_if_known.unwrap_or(false) {
            return self.or(alternate);
        }
        // [if x { false } else { x && y) ] -> false
        // [ if x { false } else { y } ] -> !x && y
        if !consequent_as_bool_if_known.unwrap_or(true) {
            if let Expression::And { left: x, right: y } = &alternate.expression {
                if self.eq(x) || self.eq(y) {
                    return Rc::new(FALSE);
                }
            }
            return self.logical_not().and(alternate);
        }

        // [if x { y } else { false }] -> x && y
        if !alternate.as_bool_if_known().unwrap_or(true) {
            return self.and(consequent);
        }
        if let Expression::Or { left: x, right: y } = &self.expression {
            match &consequent.expression {
                Expression::LogicalNot { operand } if x.eq(operand) => {
                    // [if x || y { !x } else { z }] -> [!x && y || !x && z] -> !x && (y || z)
                    return consequent.and(y.or(alternate));
                }
                Expression::ConditionalExpression {
                    condition,
                    consequent: a,
                    alternate: b,
                } => {
                    // [if x || y { if x {a} else {b} } else {b}] -> if x {a} else {b}
                    if x.eq(condition) && b.eq(&alternate) {
                        return x.conditional_expression(a.clone(), alternate);
                    }

                    // [if x || y { if y {a} else {b} } else {b}] -> if y {a} else {b}
                    if y.eq(condition) && b.eq(&alternate) {
                        return y.conditional_expression(a.clone(), alternate);
                    }

                    // [if x || y { if x {a} else {b} } else {a}] -> if y {b} else {a}
                    if x.eq(condition) && a.eq(&alternate) {
                        return y.conditional_expression(b.clone(), alternate);
                    }

                    // [if x || y { if y {a} else {b} } else {a}] -> if x {b} else {a}
                    if y.eq(condition) && a.eq(&alternate) {
                        return x.conditional_expression(b.clone(), alternate);
                    }
                }
                _ => (),
            }
        }

        // [if c { true join (c || d) } else { e }] -> c || e
        if let Expression::Join { left, right } = &consequent.expression {
            if left.as_bool_if_known().unwrap_or(false) {
                if let Expression::Or { left, .. } = &right.expression {
                    if self.eq(left) {
                        return self.or(alternate);
                    }
                }
            }
        }

        // if self { consequent } else { alternate } implies self in the consequent and !self in the alternate
        if !matches!(self.expression, Expression::Or { .. }) {
            if consequent.expression_size <= k_limits::MAX_EXPRESSION_SIZE / 10 {
                consequent = consequent.refine_with(self, 35);
            }
            if alternate.expression_size < k_limits::MAX_EXPRESSION_SIZE / 10 {
                alternate = alternate.refine_with(&not_self, 35);
            } else if let Expression::ConditionalExpression {
                condition: c,
                consequent: x,
                alternate: y,
            } = &alternate.expression
            {
                if let Expression::Or {
                    left: cl,
                    right: cr,
                } = &c.expression
                {
                    if self.eq(cl) {
                        alternate = cr.conditional_expression(x.clone(), y.clone());
                    } else if self.eq(cr) {
                        alternate = cl.conditional_expression(x.clone(), y.clone());
                    }
                }
            }
        }

        //[if x != 0 { x / c } else { 0 }] -> x / c
        if alternate.is_zero() {
            match &self.expression {
                Expression::Ne { left: x1, right } if right.is_zero() => {
                    if let Expression::Div { left: x2, right: c } = &consequent.expression {
                        if x1.eq(x2) && matches!(&c.expression, Expression::CompileTimeConstant(..))
                        {
                            return x1.divide(c.clone());
                        }
                    }
                }
                _ => {}
            }
        }

        if let Expression::ConditionalExpression {
            condition: c2,
            consequent: a,
            alternate: b,
        } = &consequent.expression
        {
            // [if self { if self { a } else { b } } else { c }] -> if self { a } else { b }
            if self.eq(c2) {
                return self.conditional_expression(a.clone(), alternate);
            }

            // [if self { if c2 { a } else { b } } else { b }] -> if condition && c2 { a } else { b }
            if b.eq(&alternate) {
                return self
                    .and(c2.clone())
                    .conditional_expression(a.clone(), alternate);
            }
            // [if self { if c2 { a } else { b } } else { a }] -> if self && !c2 { b } else { a }
            if a.eq(&alternate) {
                return self
                    .and(c2.logical_not())
                    .conditional_expression(b.clone(), alternate);
            }
        }

        if let Expression::ConditionalExpression {
            condition: c2,
            consequent: a,
            alternate: b,
        } = &alternate.expression
        {
            // [if self { consequent } else { if self { a } else { b } }] -> if self { consequent } else { b }
            if self.eq(c2) {
                return self.conditional_expression(consequent, b.clone());
            }

            // [if self { a } else { if c2 { a } else { b } }] -> if self || c2 { a } else { b }
            if a.eq(&consequent) {
                return self
                    .or(c2.clone())
                    .conditional_expression(consequent, b.clone());
            }

            // [if x == y { consequent } else { if x == z  { a } else { b } } ] -> switch x { y => consequent, z => a, _ => b }
            if let (
                Expression::Equals { left: x, right: y },
                Expression::Equals { left: x1, right: z },
            ) = (&self.expression, &c2.expression)
            {
                if x.eq(x1) {
                    return x.switch(
                        vec![(y.clone(), consequent), (z.clone(), a.clone())],
                        b.clone(),
                    );
                }
            }

            // [if y == x { consequent } else { if z == x  { a } else { b } } ] -> switch x { y => consequent, z => a, _ => b }
            if let (
                Expression::Equals { left: y, right: x },
                Expression::Equals { left: z, right: x1 },
            ) = (&self.expression, &c2.expression)
            {
                if x.eq(x1) {
                    return x.switch(
                        vec![(y.clone(), consequent), (z.clone(), a.clone())],
                        b.clone(),
                    );
                }
            }

            // [if c { a } else { if c && d { .. } else { b } }] -> if c { a } else { b }
            if let Expression::ConditionalExpression {
                condition,
                alternate: b,
                ..
            } = &alternate.expression
            {
                if condition.implies(self) {
                    return self.conditional_expression(consequent, b.clone());
                }
            }
        }

        // [if x == y { consequent } else { switch x { z  => a, _ => b } ] -> switch x { y => consequent, z => a, _ => b }
        if let (
            Expression::Equals { left: x, right: y },
            Expression::Switch {
                discriminator,
                cases,
                default,
            },
        ) = (&self.expression, &alternate.expression)
        {
            if x.eq(discriminator) {
                let mut cases = cases.clone();
                cases.push((y.clone(), consequent));
                return discriminator.switch(cases, default.clone());
            }
        }

        // [if y == x { consequent } else { switch x { z  => a, _ => b } ] -> switch x { y => consequent, z => a, _ => b }
        if let (
            Expression::Equals { left: y, right: x },
            Expression::Switch {
                discriminator,
                cases,
                default,
            },
        ) = (&self.expression, &alternate.expression)
        {
            if x.eq(discriminator) {
                let mut cases = cases.clone();
                cases.push((y.clone(), consequent));
                return discriminator.switch(cases, default.clone());
            }
        }

        let mut expression_size = self
            .expression_size
            .saturating_add(consequent.expression_size)
            .saturating_add(alternate.expression_size);
        let mut consequent_type = consequent.expression.infer_type();
        let mut alternate_type = alternate.expression.infer_type();
        // In this context not primitive is expected to indicate that the value is a default value obtained
        // via an unspecialized summary from a generic function.
        if !consequent_type.is_primitive() && alternate_type.is_primitive() {
            consequent = consequent.try_to_retype_as(alternate_type);
            consequent_type = consequent.expression.infer_type();
        } else if consequent_type.is_primitive() && !alternate_type.is_primitive() {
            alternate = alternate.try_to_retype_as(consequent_type);
            alternate_type = alternate.expression.infer_type();
        };
        if consequent_type != alternate_type
            && !(consequent_type.is_integer() && alternate_type.is_integer())
            && !(consequent.is_top() || alternate.is_top())
        {
            debug!(
                "conditional with mismatched types  {:?}: {:?}     {:?}: {:?}",
                consequent_type, consequent, alternate_type, alternate
            );
            return Rc::new(TOP);
        }
        let mut condition = self.clone();
        if expression_size > k_limits::MAX_EXPRESSION_SIZE {
            let condition_plus_consequent = self
                .expression_size
                .saturating_add(consequent.expression_size);
            if condition_plus_consequent < k_limits::MAX_EXPRESSION_SIZE - 1 {
                debug!("alternate abstracted {:?}", alternate);
                alternate = AbstractValue::make_from(alternate.expression.clone(), u64::MAX);
                expression_size = condition_plus_consequent + 1;
            } else {
                let condition_plus_alternate = self
                    .expression_size
                    .saturating_add(alternate.expression_size);
                if condition_plus_alternate < k_limits::MAX_EXPRESSION_SIZE - 1 {
                    debug!("consequent abstracted {:?}", consequent);
                    consequent = AbstractValue::make_from(consequent.expression.clone(), u64::MAX);
                    expression_size = condition_plus_alternate + 1;
                } else {
                    let consequent_plus_alternate = consequent
                        .expression_size
                        .saturating_add(alternate.expression_size);
                    if consequent_plus_alternate < k_limits::MAX_EXPRESSION_SIZE - 1 {
                        debug!("condition abstracted {:?}", condition);
                        condition =
                            AbstractValue::make_from(condition.expression.clone(), u64::MAX);
                        expression_size = consequent_plus_alternate + 1;
                    }
                }
            }
        }
        if consequent.is_top() {
            return consequent;
        }
        if alternate.is_top() {
            return alternate;
        }
        AbstractValue::make_from(
            ConditionalExpression {
                condition,
                consequent,
                alternate,
            },
            expression_size,
        )
    }

    /// Returns an element that is "*self".
    #[logfn_inputs(TRACE)]
    fn dereference(&self, target_type: ExpressionType) -> Rc<AbstractValue> {
        match &self.expression {
            Expression::Bottom | Expression::Top => self.clone(),
            Expression::Cast {
                operand,
                target_type: cast_type,
            } => {
                checked_assume!(
                    *cast_type == ExpressionType::NonPrimitive
                        || *cast_type == ExpressionType::ThinPointer
                );
                operand.dereference(target_type)
            }
            Expression::CompileTimeConstant(..) => self.clone(),
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => condition.conditional_expression(
                consequent.dereference(target_type),
                alternate.dereference(target_type),
            ),
            Expression::HeapBlock { .. } => self.clone(),
            Expression::Join { left, right } => left
                .dereference(target_type)
                .join(right.dereference(target_type)),
            Expression::Offset { .. } => {
                let path = Path::get_as_path(self.clone());
                let deref_path = Path::new_deref(path, target_type);
                if let PathEnum::Computed { value }
                | PathEnum::HeapBlock { value }
                | PathEnum::Offset { value } = &deref_path.value
                {
                    value.clone()
                } else {
                    AbstractValue::make_typed_unknown(target_type, deref_path)
                }
            }
            Expression::InitialParameterValue { path, .. } => {
                AbstractValue::make_initial_parameter_value(
                    target_type,
                    Path::new_qualified(path.clone(), Rc::new(PathSelector::Deref)),
                )
            }
            Expression::Reference(path) => {
                if target_type != ExpressionType::NonPrimitive {
                    // We don't have to shallow copy the value at the  source path, so *&p is just p.
                    if let PathEnum::Computed { value }
                    | PathEnum::HeapBlock { value }
                    | PathEnum::Offset { value } = &path.value
                    {
                        return value.clone();
                    }
                }
                AbstractValue::make_typed_unknown(target_type, path.clone())
            }
            Expression::Switch {
                discriminator,
                cases,
                default,
            } => discriminator.switch(
                cases
                    .iter()
                    .map(|(case_val, result_val)| {
                        (case_val.clone(), result_val.dereference(target_type))
                    })
                    .collect(),
                default.dereference(target_type),
            ),
            Expression::UninterpretedCall { path, .. } | Expression::Variable { path, .. } => {
                AbstractValue::make_typed_unknown(
                    target_type,
                    Path::new_qualified(path.clone(), Rc::new(PathSelector::Deref)),
                )
            }
            Expression::WidenedJoin { path, operand } => operand
                .dereference(target_type)
                .widen(&Path::new_deref(path.clone(), target_type)),
            _ => {
                info!(
                    "found unhandled expression that is of type reference: {:?}",
                    self.expression
                );
                AbstractValue::make_typed_unknown(target_type, Path::new_computed(Rc::new(TOP)))
            }
        }
    }

    /// Returns an element that is "self / other".
    #[logfn_inputs(TRACE)]
    fn divide(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        match (&self.expression, &other.expression) {
            (_, Expression::CompileTimeConstant(ConstantDomain::U128(c1))) if *c1 == 1 => {
                return self.clone();
            }
            // [(x * y) / x] -> y
            // [(x * y) / y] -> x
            (Expression::Mul { left: x, right: y }, _) => {
                if x.eq(&other) {
                    return y.clone();
                } else if y.eq(&other) {
                    return x.clone();
                }
            }
            (
                Expression::Cast {
                    operand,
                    target_type,
                },
                Expression::CompileTimeConstant(ConstantDomain::U128(c2)),
            ) => {
                if let Expression::Mul { left: x, right: y } = &operand.expression {
                    if x.eq(&other) {
                        // [((x * y) as target_type) / x] -> y as target_type
                        return y.cast(*target_type);
                    } else if y.eq(&other) {
                        // [((x * y) as target_type) / y] -> x as target_type
                        return x.cast(*target_type);
                    } else {
                        // [((c1 * y) as t) / c2] -> ((c1 / c2) * y) as t if c1 >= c2 and c1 % c2 == 0
                        if let Expression::CompileTimeConstant(ConstantDomain::U128(c1)) =
                            &x.expression
                        {
                            if *c1 > *c2 && *c1 % *c2 == 0 {
                                return x.divide(other).multiply(y.clone()).cast(*target_type);
                            }
                        }
                    }
                }
            }
            _ => (),
        }
        self.try_to_constant_fold_and_distribute_binary_op(
            other,
            ConstantDomain::div,
            Self::divide,
            |l, r| AbstractValue::make_binary(l, r, |left, right| Expression::Div { left, right }),
        )
    }

    /// Returns an abstract value that describes if `tag` is *not* attached to `self`.
    #[logfn_inputs(TRACE)]
    fn does_not_have_tag(&self, tag: &Tag) -> Rc<AbstractValue> {
        self.has_tag(tag).logical_not()
    }

    /// Returns an element that is "self == other".
    #[logfn_inputs(TRACE)]
    fn equals(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        // [x == c] -> c == x
        if !self.is_compile_time_constant() && other.is_compile_time_constant() {
            // Normalize binary expressions so that if only one of the operands is a constant, it is
            // always the left operand.
            return other.equals(self.clone());
        }
        match (&self.expression, &other.expression) {
            // true == x -> x
            (Expression::CompileTimeConstant(ConstantDomain::True), _) => {
                return other.clone();
            }
            // false == x -> !x
            (Expression::CompileTimeConstant(ConstantDomain::False), _) => {
                return other.logical_not();
            }
            // [(x as *t) == (y as *t)] -> x == y if known at compile time
            (
                Expression::Cast {
                    operand: x,
                    target_type: tt1,
                },
                Expression::Cast {
                    operand: y,
                    target_type: tt2,
                },
            ) if *tt1 == ExpressionType::ThinPointer && *tt2 == ExpressionType::ThinPointer => {
                let operands_are_equal = x.equals(y.clone());
                if operands_are_equal.is_compile_time_constant() {
                    return operands_are_equal;
                }
            }
            // [not null == (0 as *T)] -> false
            (
                _,
                Expression::Cast {
                    operand,
                    target_type,
                },
            ) if *target_type == ExpressionType::ThinPointer
                && operand.is_zero()
                && self.is_non_null() =>
            {
                return Rc::new(FALSE);
            }

            (
                Expression::HeapBlock {
                    abstract_address: a1,
                    ..
                },
                Expression::HeapBlock {
                    abstract_address: a2,
                    ..
                },
            ) => {
                return if *a1 == *a2 {
                    Rc::new(TRUE)
                } else {
                    Rc::new(FALSE)
                };
            }
            // [(widened == val)] -> if !interval(widened).intersect(interval(val)) { false } else { unknown == val }
            (Expression::WidenedJoin { path, .. }, _) => {
                let widened_interval = self.get_cached_interval();
                let val_interval = other.get_cached_interval();
                if !widened_interval.is_bottom()
                    && !val_interval.is_bottom()
                    && widened_interval.intersect(&val_interval).is_bottom()
                {
                    return Rc::new(FALSE);
                } else if self.expression_size.saturating_add(other.expression_size)
                    > k_limits::MAX_EXPRESSION_SIZE / 2
                    || self.expression.contains_local_variable(false)
                {
                    return AbstractValue::make_typed_unknown(
                        other.expression.infer_type(),
                        path.clone(),
                    )
                    .equals(other);
                };
            }
            // [(val == widened)] -> if !interval(widened).intersect(interval(val)) { false } else { val == unknown }
            (_, Expression::WidenedJoin { path, .. }) => {
                let val_interval = self.get_cached_interval();
                let widened_interval = other.get_cached_interval();
                if !widened_interval.is_bottom()
                    && !val_interval.is_bottom()
                    && widened_interval.intersect(&val_interval).is_bottom()
                {
                    return Rc::new(FALSE);
                } else if self.expression_size.saturating_add(other.expression_size)
                    > k_limits::MAX_EXPRESSION_SIZE / 2
                    || other.expression.contains_local_variable(false)
                {
                    return self.equals(AbstractValue::make_typed_unknown(
                        other.expression.infer_type(),
                        path.clone(),
                    ));
                };
            }

            // [c3 == (c ? v1 : v2)] -> !c if v1 != c3 && v2 == c3
            // [c3 == (c ? v1 : v2)] -> c if v1 == c3 && v2 != c3
            // [c3 == (c ? v1 : v2)] -> true if v1 == c3 && v2 == c3
            // [c3 == (c ? v1 : v2)] -> c ? (c3 == v1) : (c3 == v2)
            (
                Expression::CompileTimeConstant(..),
                Expression::ConditionalExpression {
                    condition: c,
                    consequent: v1,
                    alternate: v2,
                    ..
                },
            ) if !v1.is_top() && !v2.is_top() => {
                let self_eq_v2 = self.equals(v2.clone()).as_bool_if_known().unwrap_or(false);
                if v1
                    .not_equals(self.clone())
                    .as_bool_if_known()
                    .unwrap_or(false)
                    && self_eq_v2
                {
                    return c.logical_not();
                }
                if self.equals(v1.clone()).as_bool_if_known().unwrap_or(false) {
                    if self
                        .not_equals(v2.clone())
                        .as_bool_if_known()
                        .unwrap_or(false)
                    {
                        return c.clone();
                    } else if self_eq_v2 {
                        return Rc::new(TRUE);
                    }
                }
                if self.eq(&other) && !self.expression.infer_type().is_floating_point_number() {
                    return Rc::new(TRUE);
                }
                if v1.expression_size < k_limits::MAX_EXPRESSION_SIZE / 10
                    && v2.expression_size < k_limits::MAX_EXPRESSION_SIZE / 10
                {
                    return c
                        .conditional_expression(self.equals(v1.clone()), self.equals(v2.clone()));
                }
            }
            // [0 == !x] -> x when x is Boolean. Canonicalize it to the latter.
            (
                Expression::CompileTimeConstant(ConstantDomain::U128(val)),
                Expression::LogicalNot { operand },
            ) => {
                if *val == 0 && operand.expression.infer_type() == ExpressionType::Bool {
                    return operand.clone();
                }
            }
            // [0 == c * x] -> 0 == x
            (Expression::CompileTimeConstant(z), Expression::Mul { left: c, right: x })
                if z.is_zero() && c.is_compile_time_constant() =>
            {
                return self.equals(x.clone());
            }
            // [0 == (0 % x)] -> true
            (Expression::CompileTimeConstant(z), Expression::Rem { left: c, .. })
                if z.is_zero() && c.is_zero() =>
            {
                return Rc::new(TRUE);
            }

            // [0 == (1 << x)] -> false (we can assume no overflows occur)
            (
                Expression::CompileTimeConstant(ConstantDomain::U128(0)),
                Expression::Shl { left, .. },
            ) => {
                if let Expression::CompileTimeConstant(ConstantDomain::U128(1)) = left.expression {
                    return Rc::new(FALSE);
                }
            }
            // [0 == x] -> !x when x is a Boolean. Canonicalize it to the latter.
            // [1 == x] -> x when x is a Boolean. Canonicalize it to the latter.
            (Expression::CompileTimeConstant(ConstantDomain::U128(val)), x) => {
                if x.infer_type() == ExpressionType::Bool {
                    return if *val == 0 {
                        other.logical_not()
                    } else {
                        other.clone()
                    };
                }
            }
            // [(if x { y } else { z }) == z]  -> [if x { y == z } else { true }] -> !x || y == z
            (
                Expression::ConditionalExpression {
                    condition: x,
                    consequent: y,
                    alternate: z,
                },
                _,
            ) if z.eq(&other) => {
                return x.logical_not().or(y.equals(z.clone()));
            }
            // [z == (if x { y } else { z })]  -> [if x { y == z } else { true }] -> !x || y == z
            (
                _,
                Expression::ConditionalExpression {
                    condition: x,
                    consequent: y,
                    alternate: z,
                },
            ) if z.eq(self) => {
                return x.logical_not().or(y.equals(z.clone()));
            }
            // [(if x { y } else { z }) == a]  -> [if x { y == a } else { z == a }]
            (
                Expression::ConditionalExpression {
                    condition: x,
                    consequent: y,
                    alternate: z,
                },
                _,
            ) => {
                if self.expression_size + other.expression_size * 2 < k_limits::MAX_EXPRESSION_SIZE
                    && !y.is_top()
                    && !z.is_top()
                {
                    return x
                        .conditional_expression(y.equals(other.clone()), z.equals(other.clone()));
                }
            }
            // [c1 == (c2 * x)] -> (c1 / c2) == x
            (Expression::CompileTimeConstant(..), Expression::Mul { left: c2, right: x })
                if c2.is_compile_time_constant() && self.expression.infer_type().is_integer() =>
            {
                debug_checked_assume!(!c2.is_zero()); // otherwise constant folding would have reduced the Mul
                return self.divide(c2.clone()).equals(x.clone());
            }
            (Expression::Reference { .. }, Expression::Cast { .. })
            | (Expression::Cast { .. }, Expression::Reference { .. }) => {
                return Rc::new(FALSE);
            }
            _ => {
                // If self and other are the same expression and the expression could not result in
                // NaN we can simplify this to true.
                if self.eq(&other) && !self.expression.infer_type().is_floating_point_number() {
                    return Rc::new(TRUE);
                }
            }
        }
        self.try_to_constant_fold_and_distribute_binary_op(
            other,
            ConstantDomain::equals,
            Self::equals,
            |l, r| {
                AbstractValue::make_binary(l, r, |left, right| Expression::Equals { left, right })
            },
        )
    }

    /// Extracts a subexpression that must be true for the overall expression to be true
    /// and which contain no references to local variables of the current function.
    #[logfn_inputs(TRACE)]
    fn extract_promotable_conjuncts(&self, is_post_condition: bool) -> Option<Rc<AbstractValue>> {
        if let Expression::And { left, right } = &self.expression {
            if let Some(left_conjunct) = left.extract_promotable_conjuncts(is_post_condition) {
                if let Some(right_conjunct) = right.extract_promotable_conjuncts(is_post_condition)
                {
                    Some(left_conjunct.and(right_conjunct))
                } else {
                    Some(left_conjunct)
                }
            } else {
                right.extract_promotable_conjuncts(is_post_condition)
            }
        } else if !self.expression.contains_local_variable(is_post_condition)
            && self.as_bool_if_known().unwrap_or(true)
        {
            Some(self.clone())
        } else {
            None
        }
    }

    /// Extracts a subexpression that will make the overall expression true if it is true
    /// and which contain no references to local variables of the current function.
    #[logfn_inputs(TRACE)]
    fn extract_promotable_disjuncts(&self, is_post_condition: bool) -> Option<Rc<AbstractValue>> {
        match &self.expression {
            Expression::And { left, right } => {
                if let Some(left_disjunct) = left.extract_promotable_disjuncts(is_post_condition) {
                    if let Some(right_disjunct) =
                        right.extract_promotable_disjuncts(is_post_condition)
                    {
                        return Some(left_disjunct.and(right_disjunct));
                    }
                }
                None
            }
            Expression::Or { left, right } => {
                if let Some(left_disjunct) = left.extract_promotable_disjuncts(is_post_condition) {
                    if let Some(right_conjunct) =
                        right.extract_promotable_disjuncts(is_post_condition)
                    {
                        Some(left_disjunct.or(right_conjunct))
                    } else {
                        Some(left_disjunct)
                    }
                } else {
                    right.extract_promotable_disjuncts(is_post_condition)
                }
            }
            _ => {
                if !self.expression.contains_local_variable(is_post_condition)
                    && self.as_bool_if_known().unwrap_or(true)
                {
                    Some(self.clone())
                } else {
                    None
                }
            }
        }
    }

    /// Returns an element that is "self >= other".
    #[logfn_inputs(TRACE)]
    fn greater_or_equal(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        // [x >= c] -> c <= x
        if !self.is_compile_time_constant() && other.is_compile_time_constant() {
            // Normalize binary expressions so that if only one of the operands is a constant, it is
            // always the left operand.
            return other.less_or_equal(self.clone());
        }
        if let Some(result) = self
            .get_cached_interval()
            .greater_or_equal(&other.get_cached_interval())
        {
            return Rc::new(result.into());
        }
        match (&self.expression, &other.expression) {
            // [(c ? v1 : v2) >= c3] -> c ? (v1 >= c3) : (v2 >= c3)
            (
                Expression::ConditionalExpression {
                    condition: c,
                    consequent: v1,
                    alternate: v2,
                    ..
                },
                Expression::CompileTimeConstant(..),
            ) if !v1.is_top() && !v2.is_top() => {
                return c.conditional_expression(
                    v1.greater_or_equal(other.clone()),
                    v2.greater_or_equal(other.clone()),
                );
            }
            // [c3 >= (c ? v1 : v2)] -> c ? (c3 >= v1) : (c3 >= v2 )
            (
                Expression::CompileTimeConstant(..),
                Expression::ConditionalExpression {
                    condition: c,
                    consequent: v1,
                    alternate: v2,
                    ..
                },
            ) if !v1.is_top() && !v2.is_top() => {
                return c.conditional_expression(
                    self.greater_or_equal(v1.clone()),
                    self.greater_or_equal(v2.clone()),
                );
            }
            // [(c1 * x) >= c2] -> x >= c2 / c1
            (Expression::Mul { left: c1, right: x }, _)
                if c1.is_compile_time_constant()
                    && other.is_compile_time_constant()
                    && other.expression.infer_type().is_integer() =>
            {
                debug_checked_assume!(!c1.is_zero()); // otherwise constant folding would have reduced the Mul
                return x.greater_or_equal(c1.divide(other.clone()));
            }
            // [c1 >= (c2 * x)] -> x < c1 / c2
            (_, Expression::Mul { left: c2, right: x })
                if self.is_compile_time_constant()
                    && c2.is_compile_time_constant()
                    && self.expression.infer_type().is_integer() =>
            {
                debug_checked_assume!(!c2.is_zero()); // otherwise constant folding would have reduced the Mul
                return x.less_than(self.divide(c2.clone()));
            }

            _ => {}
        }
        self.try_to_constant_fold_and_distribute_binary_op(
            other,
            ConstantDomain::greater_or_equal,
            Self::greater_or_equal,
            |l, r| {
                AbstractValue::make_binary(l, r, |left, right| Expression::GreaterOrEqual {
                    left,
                    right,
                })
            },
        )
    }

    /// Returns an element that is "self > other".
    #[logfn_inputs(TRACE)]
    fn greater_than(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        // [x > c] -> c < x
        if !self.is_compile_time_constant() && other.is_compile_time_constant() {
            // Normalize binary expressions so that if only one of the operands is a constant, it is
            // always the left operand.
            return other.less_than(self.clone());
        }
        if let Some(result) = self
            .get_cached_interval()
            .greater_than(other.get_cached_interval().as_ref())
        {
            return Rc::new(result.into());
        }
        // [0 > x] -> false if x is unsigned
        if self.is_zero() && other.expression.infer_type().is_unsigned_integer() {
            return Rc::new(FALSE);
        }
        match (&self.expression, &other.expression) {
            // [(c ? v1 : v2) > c3] -> c ? (v1 > c3) : (v2 > c3)
            (
                Expression::ConditionalExpression {
                    condition: c,
                    consequent: v1,
                    alternate: v2,
                    ..
                },
                Expression::CompileTimeConstant(..),
            ) if !v1.is_top() && !v2.is_top() => {
                return c.conditional_expression(
                    v1.greater_than(other.clone()),
                    v2.greater_than(other.clone()),
                );
            }
            // [c3 > (c ? v1 : v2)] -> c ? (c3 > v1) : (c3 > v2 )
            (
                Expression::CompileTimeConstant(..),
                Expression::ConditionalExpression {
                    condition: c,
                    consequent: v1,
                    alternate: v2,
                    ..
                },
            ) if !v1.is_top() && !v2.is_top() => {
                return c.conditional_expression(
                    self.greater_than(v1.clone()),
                    self.greater_than(v2.clone()),
                );
            }
            // [(c1 * x) > c2] -> x > c2 / c1
            (Expression::Mul { left: c1, right: x }, _)
                if c1.is_compile_time_constant()
                    && other.is_compile_time_constant()
                    && other.expression.infer_type().is_integer() =>
            {
                debug_checked_assume!(!c1.is_zero()); // otherwise constant folding would have reduced the Mul
                return x.greater_than(c1.divide(other.clone()));
            }
            // [c1 > (c2 * x)] -> x <= c1 / c2
            (_, Expression::Mul { left: c2, right: x })
                if self.is_compile_time_constant()
                    && c2.is_compile_time_constant()
                    && self.expression.infer_type().is_integer() =>
            {
                debug_checked_assume!(!c2.is_zero()); // otherwise constant folding would have reduced the Mul
                return x.less_or_equal(self.divide(c2.clone()));
            }
            // [x > x] -> false
            _ => {
                if self.eq(&other) {
                    return Rc::new(FALSE);
                }
            }
        }

        self.try_to_constant_fold_and_distribute_binary_op(
            other,
            ConstantDomain::greater_than,
            Self::greater_than,
            |l, r| {
                AbstractValue::make_binary(l, r, |left, right| Expression::GreaterThan {
                    left,
                    right,
                })
            },
        )
    }

    /// Returns an abstract value that describes whether `tag` is attached to `self` or not.
    #[logfn_inputs(TRACE)]
    fn has_tag(&self, tag: &Tag) -> Rc<AbstractValue> {
        if self.is_bottom() || self.is_top() {
            self.clone()
        } else {
            Rc::new(self.get_cached_tags().has_tag(tag).into())
        }
    }

    /// Returns true if "self => other" is known at compile time to be true.
    /// Returning false does not imply the implication is false, just that we do not know.
    ///
    /// Important: keep the performance of this function proportional to the size of self.
    #[logfn_inputs(TRACE)]
    fn implies(&self, other: &Rc<AbstractValue>) -> bool {
        if self.is_bottom() || self.is_top() || other.is_bottom() || other.is_top() {
            return false;
        }

        // x => true, is always true
        // false => x, is always true
        // x => x, is always true
        if other.as_bool_if_known().unwrap_or(false)
            || !self.as_bool_if_known().unwrap_or(true)
            || (self.eq(other))
        {
            return true;
        }

        // x && y => x
        // y && x => x
        if let Expression::And { left, right } = &self.expression {
            return left.implies(other) || right.implies(other);
        }

        // x => x || y
        // x => y || x
        if let Expression::Or { left, right } = &other.expression {
            return self.implies(left) || self.implies(right);
        }
        false
    }

    /// Returns true if "self => !other" is known at compile time to be true.
    /// Returning false does not imply the implication is false, just that we do not know.
    #[logfn_inputs(TRACE)]
    fn implies_not(&self, other: &Rc<AbstractValue>) -> bool {
        if self.is_bottom() || self.is_top() || other.is_bottom() || other.is_top() {
            return false;
        }

        // x => !false, is always true
        // false => !x, is always true
        if !other.as_bool_if_known().unwrap_or(true) || !self.as_bool_if_known().unwrap_or(true) {
            return true;
        };
        // !x => !x
        if let Expression::LogicalNot { operand } = &self.expression {
            return operand.eq(other);
        }
        false
    }

    /// Returns self.f(other) where f is an intrinsic binary function.
    #[logfn_inputs(TRACE)]
    fn intrinsic_binary(&self, other: Self, name: KnownNames) -> Self {
        match (&self.expression, &other.expression) {
            (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) => {
                return Rc::new(v1.intrinsic_binary(v2, name).into());
            }
            (
                Expression::ConditionalExpression {
                    condition,
                    consequent,
                    alternate,
                },
                _,
            ) => {
                return condition.conditional_expression(
                    consequent.intrinsic_binary(other.clone(), name),
                    alternate.intrinsic_binary(other.clone(), name),
                );
            }
            (
                _,
                Expression::ConditionalExpression {
                    condition,
                    consequent,
                    alternate,
                },
            ) => {
                return condition.conditional_expression(
                    self.intrinsic_binary(consequent.clone(), name),
                    self.intrinsic_binary(alternate.clone(), name),
                );
            }
            (Expression::Join { left, right }, _) => {
                return left
                    .intrinsic_binary(other.clone(), name)
                    .join(right.intrinsic_binary(other, name));
            }
            (_, Expression::Join { left, right }) => {
                return self
                    .intrinsic_binary(left.clone(), name)
                    .join(self.intrinsic_binary(right.clone(), name));
            }
            _ => {}
        };
        AbstractValue::make_from(
            Expression::IntrinsicBinary {
                left: self.clone(),
                right: other,
                name,
            },
            self.expression_size.saturating_add(1),
        )
    }

    /// Returns (self as u(8|16|32|64|128)).f() where f is an intrinsic bit vector unary function.
    #[logfn_inputs(TRACE)]
    fn intrinsic_bit_vector_unary(&self, bit_length: u8, name: KnownNames) -> Self {
        match &self.expression {
            Expression::CompileTimeConstant(v1) => {
                let result = v1.intrinsic_bit_vector_unary(bit_length, name);
                if result != ConstantDomain::Bottom {
                    return Rc::new(result.into());
                }
            }
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => {
                return condition.conditional_expression(
                    consequent.intrinsic_bit_vector_unary(bit_length, name),
                    alternate.intrinsic_bit_vector_unary(bit_length, name),
                );
            }
            Expression::Join { left, right } => {
                return left
                    .intrinsic_bit_vector_unary(bit_length, name)
                    .join(right.intrinsic_bit_vector_unary(bit_length, name));
            }
            _ => {}
        }
        AbstractValue::make_from(
            Expression::IntrinsicBitVectorUnary {
                operand: self.clone(),
                bit_length,
                name,
            },
            self.expression_size.saturating_add(1),
        )
    }

    /// Returns self.f() where f is an intrinsic floating point unary function.
    #[logfn_inputs(TRACE)]
    fn intrinsic_floating_point_unary(&self, name: KnownNames) -> Self {
        match &self.expression {
            Expression::CompileTimeConstant(v1) => {
                let result = v1.intrinsic_floating_point_unary(name);
                if result != ConstantDomain::Bottom {
                    return Rc::new(result.into());
                }
            }
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => {
                return condition.conditional_expression(
                    consequent.intrinsic_floating_point_unary(name),
                    alternate.intrinsic_floating_point_unary(name),
                );
            }
            Expression::Join { left, right } => {
                return left
                    .intrinsic_floating_point_unary(name)
                    .join(right.intrinsic_floating_point_unary(name));
            }
            _ => {}
        }
        AbstractValue::make_from(
            Expression::IntrinsicFloatingPointUnary {
                operand: self.clone(),
                name,
            },
            self.expression_size.saturating_add(1),
        )
    }

    /// Returns true if "!self => other" is known at compile time to be true.
    /// Returning false does not imply the implication is false, just that we do not know.
    #[logfn_inputs(TRACE)]
    fn inverse_implies(&self, other: &Rc<AbstractValue>) -> bool {
        if let Expression::LogicalNot { operand } = &self.expression {
            return operand.implies(other);
        }
        if let Expression::Or { left, right } = &self.expression {
            // (!x && !y) => z if !x => z or !y => z
            return left.inverse_implies(other) || right.inverse_implies(other);
        }
        if let Expression::LogicalNot { operand } = &other.expression {
            return self.inverse_implies_not(operand);
        }
        // x => true, is always true
        // false => x, is always true
        if other.as_bool_if_known().unwrap_or(false) || self.as_bool_if_known().unwrap_or(false) {
            return true;
        }
        if self.expression.is_comparison() {
            self.logical_not().implies(other)
        } else {
            false
        }
    }

    /// Returns true if "!self => !other" is known at compile time to be true.
    /// Returning false does not imply the implication is false, just that we do not know.
    #[logfn_inputs(TRACE)]
    fn inverse_implies_not(&self, other: &Rc<AbstractValue>) -> bool {
        if self.eq(other) {
            return true;
        }
        if let Expression::Or { left, right } = &self.expression {
            // (!x && !y) => !z if !x => !z or !y => !z
            return left.inverse_implies_not(other) || right.inverse_implies_not(other);
        }
        if let Expression::And { left, right } = &other.expression {
            return self.inverse_implies_not(left) || self.implies_not(right);
        }
        false
    }

    /// True if the set of concrete values that correspond to this domain is empty.
    #[logfn_inputs(TRACE)]
    fn is_bottom(&self) -> bool {
        matches!(&self.expression, Expression::Bottom)
    }

    /// True if this value is a compile time constant.
    #[logfn_inputs(TRACE)]
    fn is_compile_time_constant(&self) -> bool {
        matches!(&self.expression, Expression::CompileTimeConstant(..))
    }

    /// True if the storage referenced by this expression is, or is contained in, a zeroed heap allocation.
    #[logfn_inputs(TRACE)]
    fn is_contained_in_zeroed_heap_block(&self) -> bool {
        match &self.expression {
            Expression::HeapBlock { is_zeroed, .. } => *is_zeroed,
            Expression::Offset { left, .. } => left.is_contained_in_zeroed_heap_block(),
            Expression::Reference(path)
            | Expression::InitialParameterValue { path, .. }
            | Expression::Variable { path, .. } => path.is_rooted_by_zeroed_heap_block(),
            _ => false,
        }
    }

    /// True if this value is a function constant.
    #[logfn_inputs(TRACE)]
    fn is_function(&self) -> bool {
        matches!(
            &self.expression,
            Expression::CompileTimeConstant(ConstantDomain::Function(..))
        )
    }

    /// True if its known at compile time that this value is a pointer or reference that is never null.
    /// If this function returns false, it does not mean that it is known that the value is null.
    #[logfn_inputs(TRACE)]
    fn is_non_null(&self) -> bool {
        {
            let mut cached_non_null = self.is_non_null.borrow_mut();
            let non_null_opt = cached_non_null.as_ref();
            if let Some(is_non_null) = non_null_opt {
                return *is_non_null;
            }
            *cached_non_null = Some(self.get_is_non_null());
        }
        self.is_non_null()
    }

    /// True if all possible concrete values are elements of the set corresponding to this domain.
    #[logfn_inputs(TRACE)]
    fn is_top(&self) -> bool {
        matches!(&self.expression, Expression::Top)
    }

    /// True if this value is an empty tuple, which is the sole value of the unit type.
    #[logfn_inputs(TRACE)]
    fn is_unit(&self) -> bool {
        matches!(
            &self.expression,
            Expression::CompileTimeConstant(ConstantDomain::Unit)
        )
    }

    /// True if this value is the constant 0 of some numeric type.
    #[logfn_inputs(TRACE)]
    fn is_zero(&self) -> bool {
        if let Expression::CompileTimeConstant(c) = &self.expression {
            return c.is_zero();
        }
        false
    }

    /// Returns an abstract value whose corresponding set of concrete values includes all of the values
    /// corresponding to self and other.
    #[logfn_inputs(TRACE)]
    fn join(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        // [{} join y] -> y
        if self.is_bottom() {
            return other;
        }
        // [TOP join y] -> TOP
        if self.is_top() {
            return self.clone();
        }
        // [x join {}] -> x
        if other.is_bottom() {
            return self.clone();
        }
        // [x join x] -> x
        if self.eq(&other) {
            return other;
        }
        // [x join TOP] -> TOP
        if other.is_top() {
            return other;
        }
        match (&self.expression, &other.expression) {
            // [(x join y) join (y join z)] -> x join (y join z)
            (
                Expression::Join {
                    left: x, right: y1, ..
                },
                Expression::Join { left: y2, .. },
            ) if y1.eq(y2) => {
                return x.join(other);
            }
            // [(x join y) join (z join a)] -> x join (y join (z join a))
            (
                Expression::Join {
                    left: x, right: y, ..
                },
                Expression::Join { .. },
            ) => {
                return x.join(y.join(other));
            }
            // [x_join_y join widen(x_join_y)] -> widen(x_join_y)
            (Expression::Join { .. }, Expression::WidenedJoin { operand, .. })
                if self.eq(operand) =>
            {
                return other;
            }
            // [(x join y) join y] -> x join y
            // [(x join y) join x] -> x join y
            (Expression::Join { left: x, right: y }, _) if x.eq(&other) || y.eq(&other) => {
                return self.clone();
            }
            // [x join (x join y)] -> x join y
            // [y join (x join y)] -> x join y
            (_, Expression::Join { left: x, right: y }) if x.eq(self) || y.eq(self) => {
                return other;
            }
            // [widen(x_join_y) join x_join_y] -> widen(x_join_y)
            (Expression::WidenedJoin { operand, .. }, Expression::Join { .. })
                if other.eq(operand) =>
            {
                return self.clone();
            }
            // [widen(x, p) join widen(y, p)] -> widen(x, p)
            (
                Expression::WidenedJoin { path: p1, .. },
                Expression::WidenedJoin { path: p2, .. },
            ) if p1.eq(p2) => {
                return self.clone();
            }
            // [widen(x_join_y) join x] -> widen(x_join_y)
            // [widen(x_join_y) join y] -> widen(x_join_y)
            (Expression::WidenedJoin { operand, .. }, _) => {
                if let Expression::Join { left, right } = &operand.expression {
                    if left.eq(&other) || right.eq(&other) {
                        return self.clone();
                    }
                }
            }
            // [x join (if c { x } else { y })] -> x join y
            // [x join (if c { y } else { x })] -> x join y
            (
                _,
                Expression::ConditionalExpression {
                    consequent: x,
                    alternate: y,
                    ..
                },
            )
            | (
                _,
                Expression::ConditionalExpression {
                    consequent: y,
                    alternate: x,
                    ..
                },
            ) if self.eq(x) => {
                return x.join(y.clone());
            }
            // [x join (y join (x join z))] -> x join (y join z)
            (
                _,
                Expression::Join {
                    left: y, right: xz, ..
                },
            ) if matches!(&xz.expression, Expression::Join { .. }) => {
                if let Expression::Join {
                    left: x, right: z, ..
                } = &xz.expression
                {
                    if self.eq(x) {
                        return self.join(y.join(z.clone()));
                    }
                }
            }
            // [x join widened(x join y)] -> widened(x join y)
            // [y join widened(x join y)] -> widened(x join y)
            (_, Expression::WidenedJoin { operand, .. }) => {
                if let Expression::Join { left: x, right: y } = &operand.expression {
                    if self.eq(x) || self.eq(y) {
                        return other.clone();
                    }
                }
            }
            _ => {}
        }
        let expression_size = self.expression_size.saturating_add(other.expression_size);
        AbstractValue::make_from(
            Expression::Join {
                left: self.clone(),
                right: other,
            },
            expression_size,
        )
    }

    /// Returns an element that is "self <= other".
    #[logfn_inputs(TRACE)]
    fn less_or_equal(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        // [x <= c] -> c >= x
        if !self.is_compile_time_constant() && other.is_compile_time_constant() {
            // Normalize binary expressions so that if only one of the operands is a constant, it is
            // always the left operand.
            return other.greater_or_equal(self.clone());
        }
        if let Some(result) = self
            .get_cached_interval()
            .less_equal(&other.get_cached_interval())
        {
            return Rc::new(result.into());
        }
        // [0 <= v1] -> true if v1 is an unsigned number
        if self.is_zero() && other.expression.infer_type().is_unsigned_integer() {
            return Rc::new(TRUE);
        }
        match (&self.expression, &other.expression) {
            // [(c ? v1 : v2) <= c3] -> c ? (v1 <= c3) : (v2 <= c3)
            (
                Expression::ConditionalExpression {
                    condition: c,
                    consequent: v1,
                    alternate: v2,
                    ..
                },
                Expression::CompileTimeConstant(..),
            ) if !v1.is_top() && !v2.is_top() => {
                return c.conditional_expression(
                    v1.less_or_equal(other.clone()),
                    v2.less_or_equal(other.clone()),
                );
            }
            // [c3 <= (c ? v1 : v2)] -> c ? (c3 <= v1) : (c3 <= v2 )
            (
                Expression::CompileTimeConstant(..),
                Expression::ConditionalExpression {
                    condition: c,
                    consequent: v1,
                    alternate: v2,
                    ..
                },
            ) if !v1.is_top() && !v2.is_top() => {
                return c.conditional_expression(
                    self.less_or_equal(v1.clone()),
                    self.less_or_equal(v2.clone()),
                );
            }
            // [(if x <= y { x } else { y }) <= y] -> true
            (
                Expression::ConditionalExpression {
                    condition: c,
                    consequent: x,
                    alternate: y,
                    ..
                },
                _,
            ) if y.eq(&other) => {
                if let Expression::LessOrEqual {
                    left: x1,
                    right: y1,
                } = &c.expression
                {
                    if x1.eq(x) && y1.eq(y) {
                        return Rc::new(TRUE);
                    }
                }
            }
            // [x & c <= c] -> true
            (
                Expression::BitAnd {
                    left: _x,
                    right: c1,
                },
                Expression::CompileTimeConstant(..),
            ) if c1.eq(&other) => {
                return Rc::new(TRUE);
            }
            // [(c1 * x) <= c2] -> x <= c2 / c1
            (Expression::Mul { left: c1, right: x }, _)
                if c1.is_compile_time_constant()
                    && other.is_compile_time_constant()
                    && other.expression.infer_type().is_integer() =>
            {
                debug_checked_assume!(!c1.is_zero()); // otherwise constant folding would have reduced the Mul
                return x.less_or_equal(c1.divide(other.clone()));
            }
            // [c1 <= (c2 * x)] -> x > c1 / c2
            (_, Expression::Mul { left: c2, right: x })
                if self.is_compile_time_constant()
                    && c2.is_compile_time_constant()
                    && self.expression.infer_type().is_integer() =>
            {
                debug_checked_assume!(!c2.is_zero()); // otherwise constant folding would have reduced the Mul
                return x.greater_than(self.divide(c2.clone()));
            }
            _ => {}
        }
        self.try_to_constant_fold_and_distribute_binary_op(
            other,
            ConstantDomain::less_or_equal,
            Self::less_or_equal,
            |l, r| {
                AbstractValue::make_binary(l, r, |left, right| Expression::LessOrEqual {
                    left,
                    right,
                })
            },
        )
    }

    /// Returns an element that is self < other
    #[logfn_inputs(TRACE)]
    fn less_than(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        // [x < c] -> c > x
        if !self.is_compile_time_constant() && other.is_compile_time_constant() {
            // Normalize binary expressions so that if only one of the operands is a constant, it is
            // always the left operand.
            return other.greater_than(self.clone());
        }
        if let Some(result) = self
            .get_cached_interval()
            .less_than(other.get_cached_interval().as_ref())
        {
            return Rc::new(result.into());
        }
        match (&self.expression, &other.expression) {
            // [(c ? v1 : v2) < c3] -> c ? (v1 < c3) : (v2 < c3)
            (
                Expression::ConditionalExpression {
                    condition: c,
                    consequent: v1,
                    alternate: v2,
                    ..
                },
                Expression::CompileTimeConstant(..),
            ) if !v1.is_top() && !v2.is_top() => {
                return c.conditional_expression(
                    v1.less_than(other.clone()),
                    v2.less_than(other.clone()),
                );
            }
            // [c3 < (c ? v1 : v2)] -> c ? (c3 < v1) : (c3 < v2 )
            (
                Expression::CompileTimeConstant(..),
                Expression::ConditionalExpression {
                    condition: c,
                    consequent: v1,
                    alternate: v2,
                    ..
                },
            ) if !v1.is_top() && !v2.is_top() => {
                return c.conditional_expression(
                    self.less_than(v1.clone()),
                    self.less_than(v2.clone()),
                );
            }
            // [(c1 * x) < c2] -> x < c2 / c1
            (Expression::Mul { left: c1, right: x }, _)
                if c1.is_compile_time_constant()
                    && other.is_compile_time_constant()
                    && other.expression.infer_type().is_integer() =>
            {
                debug_checked_assume!(!c1.is_zero()); // otherwise constant folding would have reduced the Mul
                return x.less_than(c1.divide(other.clone()));
            }
            // [c1 < (c2 * x)] -> x >= c1 / c2
            (_, Expression::Mul { left: c2, right: x })
                if self.is_compile_time_constant()
                    && c2.is_compile_time_constant()
                    && self.expression.infer_type().is_integer() =>
            {
                debug_checked_assume!(!c2.is_zero()); // otherwise constant folding would have reduced the Mul
                return x.greater_or_equal(self.divide(c2.clone()));
            }
            // [(x & c1) < c2] -> true if c1 == c2 - 1 and c2 is a power of two
            (
                Expression::BitAnd {
                    left: _x,
                    right: c1,
                },
                Expression::CompileTimeConstant(ConstantDomain::U128(c2)),
            ) if c1.is_compile_time_constant() && c2.is_power_of_two() => {
                if let Expression::CompileTimeConstant(ConstantDomain::U128(c1)) = &c1.expression {
                    if *c1 == *c2 - 1 {
                        return Rc::new(TRUE);
                    }
                }
            }
            // [x < x] -> false
            _ => {
                if self.eq(&other) {
                    return Rc::new(FALSE);
                }
            }
        }
        self.try_to_constant_fold_and_distribute_binary_op(
            other,
            ConstantDomain::less_than,
            Self::less_than,
            |l, r| {
                AbstractValue::make_binary(l, r, |left, right| Expression::LessThan { left, right })
            },
        )
    }

    /// Returns an element that is "self * other".
    #[logfn_inputs(TRACE)]
    fn multiply(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        // [x * c] -> c * x
        if !self.is_compile_time_constant() && other.is_compile_time_constant() {
            // Normalize multiply expressions so that if only one of the operands is a constant, it is
            // always the left operand.
            return other.multiply(self.clone());
        }
        if let Expression::CompileTimeConstant(c1) = &self.expression {
            match c1 {
                // [0 * y] -> 0
                ConstantDomain::I128(0) | ConstantDomain::U128(0) => {
                    return self.clone();
                }
                // [1 * y] -> y
                ConstantDomain::I128(1) | ConstantDomain::U128(1) => {
                    return other;
                }
                ConstantDomain::I128(..) | ConstantDomain::U128(..) => match &other.expression {
                    // [c * (x + y)] -> (c * x) + (c * y)
                    Expression::Add { left: x, right: y } => {
                        let unsimplified_size =
                            self.expression_size.saturating_add(other.expression_size);
                        let cx_cy = self.multiply(x.clone()).addition(self.multiply(y.clone()));
                        if !cx_cy.is_bottom() && cx_cy.expression_size < unsimplified_size {
                            return cx_cy;
                        }
                    }
                    // [c1 * (c2 * y)] -> (c1 * c2) * y
                    Expression::Mul { left: x, right: y } if x.is_compile_time_constant() => {
                        return self.multiply(x.clone()).multiply(y.clone());
                    }
                    _ => {}
                },
                _ => {
                    // [c1 * (x / c2)] -> x / (c2 / c1) if c2 > c1 && c2 % c1 == 0
                    if let Expression::Div { left: x, right } = &other.expression {
                        if let Expression::CompileTimeConstant(c2) = &right.expression {
                            if let (ConstantDomain::U128(c1), ConstantDomain::U128(c2)) = (c1, c2) {
                                if c2 > c1 && c2 % c1 == 0 {
                                    let c2_div_c1: Rc<AbstractValue> = Rc::new((c2 / c1).into());
                                    return x.divide(c2_div_c1);
                                }
                            }
                        }
                    }
                }
            }
        }
        self.try_to_constant_fold_and_distribute_binary_op(
            other,
            ConstantDomain::mul,
            Self::multiply,
            |l, r| AbstractValue::make_binary(l, r, |left, right| Expression::Mul { left, right }),
        )
    }

    /// Returns an element that is true if "self * other" is not in range of target_type.
    #[logfn_inputs(TRACE)]
    fn mul_overflows(
        &self,
        other: Rc<AbstractValue>,
        target_type: ExpressionType,
    ) -> Rc<AbstractValue> {
        // [x * c] -> c * x
        if !self.is_compile_time_constant() && other.is_compile_time_constant() {
            // Normalize multiply expressions so that if only one of the operands is a constant, it is
            // always the left operand.
            return other.mul_overflows(self.clone(), target_type);
        }
        if self.is_bottom() || self.is_top() || other.is_bottom() || other.is_top() {
            return AbstractValue::make_typed_unknown(
                ExpressionType::Bool,
                Path::new_computed(TOP.into()),
            );
        }
        if let Expression::CompileTimeConstant(c1) = &self.expression {
            match c1 {
                // [0 * y] -> 0
                ConstantDomain::I128(0) | ConstantDomain::U128(0) => {
                    return Rc::new(FALSE);
                }
                // [1 * y] -> y
                ConstantDomain::I128(1) | ConstantDomain::U128(1) => {
                    return Rc::new(FALSE);
                }
                ConstantDomain::I128(..) | ConstantDomain::U128(..) => match &other.expression {
                    // [c * (x + y)] -> (c * x) + (c * y)
                    // Do not apply distribution rule because it may introduce spurious overflows

                    // [c1 * (c2 * y)] -> (c1 * c2) * y
                    Expression::Mul { left: x, right: y } if x.is_compile_time_constant() => {
                        return self
                            .multiply(x.clone())
                            .mul_overflows(y.clone(), target_type);
                    }
                    _ => {}
                },

                _ => {
                    // [overflows(c1 * (x / c2))] -> false if c2 > c1 && c2 % c1 == 0
                    if let Expression::Div { right, .. } = &other.expression {
                        if let Expression::CompileTimeConstant(c2) = &right.expression {
                            if let (ConstantDomain::U128(c1), ConstantDomain::U128(c2)) = (c1, c2) {
                                if c2 > c1 && c2 % c1 == 0 {
                                    return Rc::new(FALSE);
                                }
                            }
                        }
                    }
                }
            }
        }
        let interval = self.get_cached_interval().mul(&other.get_cached_interval());
        if interval.is_contained_in(target_type) {
            return Rc::new(FALSE);
        }
        self.try_to_constant_fold_and_distribute_typed_binary_op(
            other,
            target_type,
            ConstantDomain::mul_overflows,
            Self::mul_overflows,
            |l, r, t| {
                AbstractValue::make_typed_binary(l, r, t, |left, right, result_type| {
                    Expression::MulOverflows {
                        left,
                        right,
                        result_type,
                    }
                })
            },
        )
    }

    /// Returns an element that is "-self".
    #[logfn_inputs(TRACE)]
    fn negate(&self) -> Rc<AbstractValue> {
        // [-(x - y)] -> y - x
        if let Expression::Sub { left: x, right: y } = &self.expression {
            return y.subtract(x.clone());
        }
        self.try_to_constant_fold_and_distribute_unary_op(ConstantDomain::neg, Self::negate, |o| {
            AbstractValue::make_unary(o, |operand| Expression::Neg { operand })
        })
    }

    /// Returns an element that is "self != other".
    #[logfn_inputs(TRACE)]
    fn not_equals(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        // [x != c] -> c != x
        if !self.is_compile_time_constant() && other.is_compile_time_constant() {
            // Normalize binary expressions so that if only one of the operands is a constant, it is
            // always the left operand.
            return other.not_equals(self.clone());
        }
        match (&self.expression, &other.expression) {
            // true != x -> !x
            (Expression::CompileTimeConstant(ConstantDomain::True), _) => {
                return other.logical_not();
            }
            // false != x -> x
            (Expression::CompileTimeConstant(ConstantDomain::False), _) => {
                return other.clone();
            }
            // [0 != (1 << x)] -> true (we can assume no overflows occur)
            (
                Expression::CompileTimeConstant(ConstantDomain::U128(0)),
                Expression::Shl { left, .. },
            ) => {
                if let Expression::CompileTimeConstant(ConstantDomain::U128(1)) = left.expression {
                    return Rc::new(TRUE);
                }
            }
            // [0 != y] -> y when y is a Boolean. Canonicalize it to the latter.
            (Expression::CompileTimeConstant(ConstantDomain::U128(0)), y)
                if y.infer_type() == ExpressionType::Bool =>
            {
                return other.clone();
            }
            // [c1 != (c2 * x)] -> ( c1 / c2) != x
            (_, Expression::Mul { left: c2, right: x })
                if self.is_compile_time_constant()
                    && c2.is_compile_time_constant()
                    && self.expression.infer_type().is_integer() =>
            {
                debug_checked_assume!(!c2.is_zero()); // otherwise constant folding would have reduced the Mul
                return self.divide(c2.clone()).not_equals(x.clone());
            }

            // [c3 != (c ? v1 : v2)] -> !c if v1 == c3 && v2 != c3
            // [c3 != (c ? v1 : v2)] -> c if v1 != c3 && v2 == c3
            // [c3 != (c ? v1 : v2)] -> true if v1 != c3 && v2 != c3
            // [c3 != (c ? v1 : v2)] -> c ? (c3 != v1) : (c3 != v2)
            (
                Expression::CompileTimeConstant(..),
                Expression::ConditionalExpression {
                    condition: c,
                    consequent: v1,
                    alternate: v2,
                    ..
                },
            ) if !v1.is_top() && !v2.is_top() => {
                let v2_ne_self = v2
                    .not_equals(self.clone())
                    .as_bool_if_known()
                    .unwrap_or(false);
                if v1.equals(self.clone()).as_bool_if_known().unwrap_or(false) && v2_ne_self {
                    return c.logical_not();
                }
                if v1
                    .not_equals(self.clone())
                    .as_bool_if_known()
                    .unwrap_or(false)
                {
                    if v2.equals(self.clone()).as_bool_if_known().unwrap_or(false) {
                        return c.clone();
                    } else if v2_ne_self {
                        return Rc::new(TRUE);
                    }
                }
                if self.eq(&other) && !self.expression.infer_type().is_floating_point_number() {
                    return Rc::new(FALSE);
                }
                return c.conditional_expression(
                    self.not_equals(v1.clone()),
                    self.not_equals(v2.clone()),
                );
            }
            _ => {
                // If self and other are the same expression and the expression could not result in
                // NaN we can simplify this to false.
                if self.eq(&other) && !self.expression.infer_type().is_floating_point_number() {
                    return Rc::new(FALSE);
                }
            }
        }
        self.try_to_constant_fold_and_distribute_binary_op(
            other,
            ConstantDomain::not_equals,
            Self::not_equals,
            |l, r| AbstractValue::make_binary(l, r, |left, right| Expression::Ne { left, right }),
        )
    }

    /// Returns an element that is "!self" where self is a bool.
    #[logfn_inputs(TRACE)]
    fn logical_not(&self) -> Rc<AbstractValue> {
        match &self.expression {
            Expression::Bottom => self.clone(),
            Expression::Equals { left: x, right: y }
                if !x.expression.infer_type().is_floating_point_number() =>
            {
                // [!(x == y)] -> x != y
                x.not_equals(y.clone())
            }
            Expression::GreaterThan { left: x, right: y }
                if x.expression.infer_type().is_integer() =>
            {
                // [!(x > y)] -> x <= y
                x.less_or_equal(y.clone())
            }
            Expression::GreaterOrEqual { left: x, right: y }
                if x.expression.infer_type().is_integer() =>
            {
                // [!(x >= y)] -> x < y
                x.less_than(y.clone())
            }
            Expression::LessThan { left: x, right: y }
                if x.expression.infer_type().is_integer() =>
            {
                // [!(x < y)] -> x >= y
                x.greater_or_equal(y.clone())
            }
            Expression::LessOrEqual { left: x, right: y }
                if x.expression.infer_type().is_integer() =>
            {
                // [!(x <= y)] -> x > y
                x.greater_than(y.clone())
            }
            Expression::LogicalNot { operand } => {
                // [!!x] -> x
                operand.clone()
            }
            Expression::Ne { left: x, right: y }
                if !x.expression.infer_type().is_floating_point_number() =>
            {
                // [!(x != y)] -> x == y
                x.equals(y.clone())
            }
            Expression::Or { left: x, right }
                if matches!(right.expression, Expression::LogicalNot { .. }) =>
            {
                // [!(x || !y)] -> !x && y
                if let Expression::LogicalNot { operand: y } = &right.expression {
                    x.logical_not().and(y.clone())
                } else {
                    unreachable!()
                }
            }
            Expression::Or { left, right: y }
                if matches!(left.expression, Expression::LogicalNot { .. }) =>
            {
                // [!(!x || y)] -> x && !y
                if let Expression::LogicalNot { operand: x } = &left.expression {
                    x.and(y.logical_not())
                } else {
                    unreachable!()
                }
            }
            _ => self.try_to_constant_fold_and_distribute_unary_op(
                ConstantDomain::logical_not,
                Self::logical_not,
                |o| AbstractValue::make_unary(o, |operand| Expression::LogicalNot { operand }),
            ),
        }
    }

    /// Returns an element that is "&self + other*scale".
    #[logfn_inputs(TRACE)]
    fn offset(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        if let Expression::Offset { left, right } = &self.expression {
            left.offset(right.addition(other))
        } else if other.is_zero() {
            self.clone()
        } else {
            self.try_to_distribute_binary_op(other, Self::offset, |l, r| {
                AbstractValue::make_binary(l, r, |left, right| Expression::Offset { left, right })
            })
        }
    }

    /// Returns an element that is "self || other".
    #[logfn_inputs(TRACE)]
    #[allow(clippy::cognitive_complexity)]
    fn or(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        fn is_contained_in(x: &Rc<AbstractValue>, y: &Rc<AbstractValue>) -> bool {
            if x.eq(y) {
                return true;
            }
            if let Expression::Or { left, right } = &y.expression {
                is_contained_in(x, left) || is_contained_in(x, right)
            } else {
                false
            }
        }

        let self_as_bool = self.as_bool_if_known();
        if !self_as_bool.unwrap_or(true) {
            // [false || y] -> y
            other
        } else if self_as_bool.unwrap_or(false) || other.as_bool_if_known().unwrap_or(false) {
            // [x || true] -> true
            // [true || y] -> true
            Rc::new(TRUE)
        } else if other.is_top() || other.is_bottom() || !self.as_bool_if_known().unwrap_or(true) {
            // [self || TOP] -> TOP
            // [self || BOTTOM] -> BOTTOM
            // [false || other] -> other
            other
        } else if self.is_top() || self.is_bottom() || !other.as_bool_if_known().unwrap_or(true) {
            // [TOP || other] -> TOP
            // [BOTTOM || other] -> BOTTOM
            // [self || false] -> self
            self.clone()
        } else {
            // [x || x] -> x
            if is_contained_in(self, &other) {
                return self.clone();
            }

            // [!x || x] -> true
            if let Expression::LogicalNot { operand } = &self.expression {
                if is_contained_in(operand, &other) {
                    return Rc::new(TRUE);
                }
            }

            // [x || !x] -> true
            if let Expression::LogicalNot { operand } = &other.expression {
                if is_contained_in(operand, self) {
                    return Rc::new(TRUE);
                }
            } else if is_contained_in(&self.logical_not(), &other) {
                return Rc::new(TRUE);
            }

            // [x || (x || y)] -> x || y
            // [x || (y || x)] -> x || y
            // [(x || y) || y] -> x || y
            // [(x || y) || x] -> x || y
            if is_contained_in(self, &other) {
                return other;
            } else if is_contained_in(&other, self) {
                return self.clone();
            }

            // [self || (x && z)] -> self || z if !self => x
            if let Expression::And { left, right: z } = &other.expression {
                if self.inverse_implies(left) {
                    return self.or(z.clone());
                }
                if let Expression::LogicalNot { operand: xy } = &left.expression {
                    match &xy.expression {
                        // [x || (!(!x && y) && z)] -> x || (!y && z)
                        Expression::And {
                            left: nx,
                            right: y2,
                        } => {
                            if let Expression::LogicalNot { operand: x2 } = &nx.expression {
                                if self.eq(x2) {
                                    return self.or(y2.logical_not().and(z.clone()));
                                }
                            }
                        }
                        // [x || (!(x || y) && z)] -> x || (!y && z)
                        Expression::Or {
                            left: x2,
                            right: y2,
                        } => {
                            if self.eq(x2) {
                                return self.or(y2.logical_not().and(z.clone()));
                            }
                        }
                        _ => {}
                    }
                }
            }

            // [x || (x && y)] -> x, etc.
            if self.inverse_implies_not(&other) {
                return self.clone();
            }

            // [x || !(x && y)] -> true, etc.
            if self.inverse_implies(&other) {
                return Rc::new(TRUE);
            }

            match (&self.expression, &other.expression) {
                // [!x || x] -> true
                (Expression::LogicalNot { operand }, _) if operand.eq(&other) => {
                    return Rc::new(TRUE);
                }
                // [x || !x] -> true
                (_, Expression::LogicalNot { operand }) if operand.eq(self) => {
                    return Rc::new(TRUE);
                }

                // [(x == y) || (x != y)] -> true if x is not a floating point
                (
                    Expression::Equals {
                        left: x1,
                        right: y1,
                    },
                    Expression::Ne {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2)
                    && y1.eq(y2)
                    && !x1.expression.infer_type().is_floating_point_number() =>
                {
                    return Rc::new(TRUE);
                }

                // [x >= y || x < y] -> true if x is not a floating point
                (
                    Expression::GreaterOrEqual {
                        left: x1,
                        right: y1,
                    },
                    Expression::LessThan {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2)
                    && y1.eq(y2)
                    && !x1.expression.infer_type().is_floating_point_number() =>
                {
                    return Rc::new(TRUE);
                }
                // [x < y || x >= y] -> true if x is not a floating point
                (
                    Expression::LessThan {
                        left: x1,
                        right: y1,
                    },
                    Expression::GreaterOrEqual {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2)
                    && y1.eq(y2)
                    && !x1.expression.infer_type().is_floating_point_number() =>
                {
                    return Rc::new(TRUE);
                }
                // [x <= y || x > y] -> true if x is not a floating point
                (
                    Expression::LessOrEqual {
                        left: x1,
                        right: y1,
                    },
                    Expression::GreaterThan {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2)
                    && y1.eq(y2)
                    && !x1.expression.infer_type().is_floating_point_number() =>
                {
                    return Rc::new(TRUE);
                }
                // [x > y || x <= y] -> true if x is not a floating point
                (
                    Expression::GreaterThan {
                        left: x1,
                        right: y1,
                    },
                    Expression::LessOrEqual {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2)
                    && y1.eq(y2)
                    && !x1.expression.infer_type().is_floating_point_number() =>
                {
                    return Rc::new(TRUE);
                }

                // [x > y || x == y] -> x >= y
                // [x >= y || x == y] -> x >= y
                (
                    Expression::GreaterThan {
                        left: x1,
                        right: y1,
                    },
                    Expression::Equals {
                        left: x2,
                        right: y2,
                    },
                )
                | (
                    Expression::GreaterOrEqual {
                        left: x1,
                        right: y1,
                    },
                    Expression::Equals {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2) && y1.eq(y2) => {
                    return x1.greater_or_equal(y1.clone());
                }
                // [x == y || x > y] -> x >= y
                // [x == y || x >= y] -> x >= y
                (
                    Expression::Equals {
                        left: x1,
                        right: y1,
                    },
                    Expression::GreaterThan {
                        left: x2,
                        right: y2,
                    },
                )
                | (
                    Expression::Equals {
                        left: x1,
                        right: y1,
                    },
                    Expression::GreaterOrEqual {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2) && y1.eq(y2) => {
                    return x1.greater_or_equal(y1.clone());
                }

                // [(x == y) || (y > z)] -> y > z if z < x
                (
                    Expression::Equals { left: x, right: y1 },
                    Expression::GreaterThan { left: y2, right: z },
                ) if y1.eq(y2) => {
                    if let (
                        Expression::CompileTimeConstant(cx),
                        Expression::CompileTimeConstant(cz),
                    ) = (&x.expression, &z.expression)
                    {
                        if cz.less_than(cx).is_true() {
                            return other.clone();
                        }
                    }
                }

                // [x < y || x == y] -> x <= y
                // [x <= y || x == y] -> x <= y
                (
                    Expression::LessThan {
                        left: x1,
                        right: y1,
                    },
                    Expression::Equals {
                        left: x2,
                        right: y2,
                    },
                )
                | (
                    Expression::LessOrEqual {
                        left: x1,
                        right: y1,
                    },
                    Expression::Equals {
                        left: x2,
                        right: y2,
                    },
                )
                | (
                    Expression::LessOrEqual {
                        left: x1,
                        right: y1,
                    },
                    Expression::Equals {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2) && y1.eq(y2) => {
                    return x1.less_or_equal(y1.clone());
                }
                // [x < y || x <= y] -> x <= y
                // [x < y || x == y] -> x <= y
                // [y == x || x < y] -> x <= y
                (
                    Expression::LessThan {
                        left: x1,
                        right: y1,
                    },
                    Expression::LessOrEqual {
                        left: x2,
                        right: y2,
                    },
                )
                | (
                    Expression::LessThan {
                        left: x1,
                        right: y1,
                    },
                    Expression::Equals {
                        left: x2,
                        right: y2,
                    },
                )
                | (
                    Expression::Equals {
                        left: y1,
                        right: x1,
                    },
                    Expression::LessThan {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2) && y1.eq(y2) => {
                    return x1.less_or_equal(y2.clone());
                }
                // [x < y || x <= y] -> x <= y
                (
                    Expression::LessThan {
                        left: x1,
                        right: y1,
                    },
                    Expression::LessOrEqual {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2) && y1.eq(y2) => {
                    return other.clone();
                }
                // [x == y || x <==> y] -> x <= y
                (
                    Expression::Equals {
                        left: x1,
                        right: y1,
                    },
                    Expression::LessThan {
                        left: x2,
                        right: y2,
                    },
                ) if x1.eq(x2) && y1.eq(y2) => {
                    return x1.less_or_equal(y1.clone());
                }
                (
                    Expression::And {
                        left: x1,
                        right: y1,
                    },
                    Expression::And {
                        left: x2,
                        right: y2,
                    },
                ) => {
                    if x1.eq(x2) {
                        return if y1.logical_not().eq(y2) {
                            // [(x && y) || (x && !y)] -> x
                            x1.clone()
                        } else {
                            // [(x && y1) || (x && y2)] -> x && (y1 || y2)
                            x1.and(y1.or(y2.clone()))
                        };
                    } else if y1.eq(y2) {
                        return if x1.logical_not().eq(x2) {
                            // [(x && y) || (!x && y)] -> y
                            y1.clone()
                        } else {
                            // [(x1 && y) || (x2 && y)] -> (x1 || x2) && y
                            x1.or(x2.clone()).and(y1.clone())
                        };
                    } else if let Expression::And {
                        left: x2,
                        right: x3,
                    } = &x2.expression
                    {
                        if x1.eq(x2) {
                            // [(x && y1) || ((x && x3) && y2)] -> x && (y1 || (x3 && y2))
                            return x1.and(y1.or(x3.and(y2.clone())));
                        }
                    }
                }

                // [((c ? e : 1) == 1) || ((c ? e : 1) == 0)] -> !c || e == 0 || e == 1
                (
                    Expression::Equals {
                        left: l1,
                        right: r1,
                    },
                    Expression::Equals {
                        left: l2,
                        right: r2,
                    },
                ) if l1.eq(l2) && r1.expression.is_one() && r2.expression.is_zero() => {
                    if let Expression::ConditionalExpression {
                        condition: c,
                        consequent: e,
                        alternate: one,
                    } = &l1.expression
                    {
                        if one.expression.is_one() {
                            let not_c = c.logical_not();
                            let e_eq_0 = e.equals(Rc::new(ConstantDomain::U128(0).into()));
                            let e_eq_1 = e.equals(Rc::new(ConstantDomain::U128(1).into()));
                            return not_c.or(e_eq_0).or(e_eq_1);
                        }
                    }
                }

                // [1 == ((c ? e : 1)) || (0 == (c ? e : 1))] -> !c || 0 == e || 1 == e
                (
                    Expression::Equals {
                        left: l1,
                        right: r1,
                    },
                    Expression::Equals {
                        left: l2,
                        right: r2,
                    },
                ) if r1.eq(r2) && l1.expression.is_one() && l2.expression.is_zero() => {
                    if let Expression::ConditionalExpression {
                        condition: c,
                        consequent: e,
                        alternate: one,
                    } = &r1.expression
                    {
                        if one.expression.is_one() {
                            let not_c = c.logical_not();
                            let e_eq_0 = e.equals(Rc::new(ConstantDomain::U128(0).into()));
                            let e_eq_1 = e.equals(Rc::new(ConstantDomain::U128(1).into()));
                            return not_c.or(e_eq_0).or(e_eq_1);
                        }
                    }
                }

                // [( x ? false : y ) || x] -> x || y
                (
                    Expression::ConditionalExpression {
                        condition: x,
                        consequent: f,
                        alternate: y,
                    },
                    _,
                ) if x.eq(&other) && !f.as_bool_if_known().unwrap_or(true) => {
                    return x.or(y.clone());
                }

                // [(x && y) || x] -> x
                // [(x && y) || y] -> y
                (Expression::And { left: x, right: y }, _) if x.eq(&other) || y.eq(&other) => {
                    return other;
                }

                // [x || (x && y)] -> x
                // [y || (x && y)] -> y
                (_, Expression::And { left: x, right: y }) if x.eq(self) || y.eq(self) => {
                    return self.clone();
                }

                // [x || (!x && z)] -> x || z
                (_, Expression::And { left: y, right: z }) if self.inverse_implies(y) => {
                    return self.or(z.clone());
                }

                // [(x && y) || (!x || !y)] -> true
                (Expression::And { left: x, right: y }, Expression::Or { left, right })
                    if x.inverse_implies(left) && y.inverse_implies(right) =>
                {
                    return Rc::new(TRUE);
                }

                // [widened bool || x] -> unknown bool || x
                (Expression::WidenedJoin { path, .. }, _) => {
                    return AbstractValue::make_typed_unknown(ExpressionType::Bool, path.clone())
                        .or(other);
                }
                // [x || widened bool] -> x || unknown bool
                (_, Expression::WidenedJoin { path, .. }) => {
                    return self.or(AbstractValue::make_typed_unknown(
                        ExpressionType::Bool,
                        path.clone(),
                    ));
                }
                // [(x && !y) || !(x || y)] -> !y
                // [(x && !y) || !(y || x)] -> !y
                (Expression::And { left: x1, right }, Expression::LogicalNot { operand })
                    if matches!(right.expression, Expression::LogicalNot { .. })
                        && matches!(operand.expression, Expression::Or { .. }) =>
                {
                    if let (
                        Expression::LogicalNot { operand: y1 },
                        Expression::Or {
                            left: x2,
                            right: y2,
                        },
                    ) = (&right.expression, &operand.expression)
                    {
                        if (x1.eq(x2) && y1.eq(y2)) || (x1.eq(y2) && y1.eq(x2)) {
                            return right.clone();
                        }
                    }
                }
                // [(!x && y) || !(x || y)] -> !x
                (
                    Expression::And {
                        left: nx,
                        right: y1,
                    },
                    Expression::LogicalNot { operand },
                ) if matches!(nx.expression, Expression::LogicalNot { .. })
                    && matches!(operand.expression, Expression::Or { .. }) =>
                {
                    if let (
                        Expression::LogicalNot { operand: x1 },
                        Expression::Or {
                            left: x2,
                            right: y2,
                        },
                    ) = (&nx.expression, &operand.expression)
                    {
                        if x1.eq(x2) && y1.eq(y2) {
                            return nx.clone();
                        }
                    }
                }
                (Expression::And { left, right }, _) => {
                    match (&left.expression, &right.expression) {
                        // [(x && !y) || y] -> (x || y)
                        (_, Expression::LogicalNot { operand: y }) if y.eq(&other) => {
                            return left.or(y.clone());
                        }
                        // [(!x && y) || x] -> (x || y)
                        (Expression::LogicalNot { operand: x }, _) if x.eq(&other) => {
                            return x.or(right.clone());
                        }
                        _ => {}
                    }
                }

                (
                    Expression::Or {
                        left: x,
                        right: ynz,
                    },
                    Expression::And {
                        left: y2,
                        right: z2,
                    },
                ) => {
                    // [(x || (y && !z)) || (y && z)))] -> x || y
                    if let Expression::And {
                        left: y1,
                        right: nz,
                    } = &ynz.expression
                    {
                        if let Expression::LogicalNot { operand: z1 } = &nz.expression {
                            if y1.eq(y2) && z1.eq(z2) {
                                return x.or(y1.clone());
                            }
                        }
                    }

                    // [((x || (y && !z)) || a) || (y && z)] -> (x || y) || a
                    if let Expression::Or {
                        left: x1,
                        right: ynz1,
                    } = &x.expression
                    {
                        let a = ynz;
                        if let Expression::And {
                            left: y1,
                            right: nz,
                        } = &ynz1.expression
                        {
                            if let Expression::LogicalNot { operand: z1 } = &nz.expression {
                                if y1.eq(y2) && z1.eq(z2) {
                                    return x1.or(y1.clone()).or(a.clone());
                                }
                            }
                        }
                    }
                }

                // [(x || (y < z)) || (z == y)] -> x || (y <= z)
                (
                    Expression::Or {
                        left: x,
                        right: y_lt_z,
                    },
                    Expression::Equals {
                        left: z1,
                        right: y1,
                    },
                ) => {
                    if let Expression::LessThan {
                        left: y2,
                        right: z2,
                    } = &y_lt_z.expression
                    {
                        if y1.eq(y2) && z1.eq(z2) {
                            return x.or(y1.less_or_equal(z1.clone()));
                        }
                    }
                }

                // [x || !(x || y)] -> x || !y
                (_, Expression::LogicalNot { operand }) => match &operand.expression {
                    Expression::Or { left: x2, right: y } if self.eq(x2) => {
                        return self.or(y.logical_not());
                    }
                    _ => {}
                },

                // [!x || (x && y ? false : z)] -> !x || (!y && z)
                (
                    Expression::LogicalNot { operand: x1 },
                    Expression::ConditionalExpression {
                        condition: c,
                        consequent,
                        alternate: z,
                    },
                ) => {
                    if let Expression::And { left: x2, right: y } = &c.expression {
                        if x1.eq(x2) && !consequent.as_bool_if_known().unwrap_or(true) {
                            return self.or(y.logical_not().and(z.clone()));
                        }
                    }
                }
                _ => {}
            }
            self.try_to_constant_fold_and_distribute_binary_op(
                other,
                ConstantDomain::or,
                Self::or,
                |l, r| {
                    AbstractValue::make_binary(l, r, |left, right| Expression::Or { left, right })
                },
            )
        }
    }

    /// Adds any abstract heap addresses and strings found in the associated expression to the given set.
    #[logfn_inputs(TRACE)]
    fn record_heap_blocks_and_strings(&self, result: &mut HashSet<Rc<AbstractValue>>) {
        self.expression.record_heap_blocks_and_strings(result);
    }

    /// Returns an element that is "self % other".
    #[logfn_inputs(TRACE)]
    fn remainder(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        // [(x as t) % c] -> x % c if c.is_power_of_two() && c <= t.modulo_value()
        if let Expression::Cast {
            operand: x,
            target_type: t,
            ..
        } = &self.expression
        {
            if let Expression::CompileTimeConstant(ConstantDomain::U128(c)) = &other.expression {
                if c.is_power_of_two()
                    && other
                        .less_or_equal(t.modulo_value())
                        .as_bool_if_known()
                        .unwrap_or(false)
                {
                    return x.remainder(other);
                }
            }
        }
        self.try_to_constant_fold_and_distribute_binary_op(
            other,
            ConstantDomain::rem,
            Self::remainder,
            |l, r| AbstractValue::make_binary(l, r, |left, right| Expression::Rem { left, right }),
        )
    }

    /// If self refers to any variable in the given set, return TRUE otherwise return self.
    /// In the case where self is a conjunction apply the function to the conjuncts and return
    /// a new conjunction. The nett effect is that if self is a conjunction, such as a entry condition,
    /// it is purged of any conjuncts that depend on variables (expected to be the set of variables
    /// modified by a loop body).
    #[logfn_inputs(TRACE)]
    fn remove_conjuncts_that_depend_on(&self, variables: &HashSet<Rc<Path>>) -> Rc<AbstractValue> {
        if let Expression::And { left, right } = &self.expression {
            let purged_left = left.remove_conjuncts_that_depend_on(variables);
            let purged_right = right.remove_conjuncts_that_depend_on(variables);
            purged_left.and(purged_right)
        } else if self.uses(variables) {
            Rc::new(self::TRUE)
        } else {
            self.clone()
        }
    }

    /// Returns an element that is "self << other".
    #[logfn_inputs(TRACE)]
    fn shift_left(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        if other.is_zero() {
            return self.clone();
        }
        self.try_to_constant_fold_and_distribute_binary_op(
            other,
            ConstantDomain::shl,
            Self::shift_left,
            |l, r| AbstractValue::make_binary(l, r, |left, right| Expression::Shl { left, right }),
        )
    }

    /// Returns an element that is true if "self << other" shifts away all bits.
    #[logfn_inputs(TRACE)]
    fn shl_overflows(
        &self,
        other: Rc<AbstractValue>,
        target_type: ExpressionType,
    ) -> Rc<AbstractValue> {
        if self.is_bottom() || self.is_top() || other.is_bottom() || other.is_top() {
            return AbstractValue::make_typed_unknown(
                ExpressionType::Bool,
                Path::new_computed(TOP.into()),
            );
        }
        let interval = other.get_cached_interval();
        if interval.is_contained_in_width_of(target_type) {
            return Rc::new(FALSE);
        }
        self.try_to_constant_fold_and_distribute_typed_binary_op(
            other,
            target_type,
            ConstantDomain::shl_overflows,
            Self::shl_overflows,
            |l, r, t| {
                AbstractValue::make_typed_binary(l, r, t, |left, right, result_type| {
                    Expression::ShlOverflows {
                        left,
                        right,
                        result_type,
                    }
                })
            },
        )
    }

    /// Returns an element that is "self >> other".
    #[logfn_inputs(TRACE)]
    fn shr(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        if other.is_zero() {
            return self.clone();
        }
        self.try_to_constant_fold_and_distribute_binary_op(
            other,
            ConstantDomain::shr,
            Self::shr,
            |l, r| AbstractValue::make_binary(l, r, |left, right| Expression::Shr { left, right }),
        )
    }

    /// Returns an element that is true if "self >> other" shifts away all bits.
    #[logfn_inputs(TRACE)]
    fn shr_overflows(
        &self,
        other: Rc<AbstractValue>,
        target_type: ExpressionType,
    ) -> Rc<AbstractValue> {
        if self.is_bottom() || self.is_top() || other.is_bottom() || other.is_top() {
            return AbstractValue::make_typed_unknown(
                ExpressionType::Bool,
                Path::new_computed(TOP.into()),
            );
        }
        let interval = &other.get_cached_interval();
        if interval.is_contained_in_width_of(target_type) {
            return Rc::new(FALSE);
        }
        self.try_to_constant_fold_and_distribute_typed_binary_op(
            other,
            target_type,
            ConstantDomain::shr_overflows,
            Self::shr_overflows,
            |l, r, t| {
                AbstractValue::make_typed_binary(l, r, t, |left, right, result_type| {
                    Expression::ShrOverflows {
                        left,
                        right,
                        result_type,
                    }
                })
            },
        )
    }

    /// Returns an element that is "self - other".
    #[logfn_inputs(TRACE)]
    fn subtract(&self, other: Rc<AbstractValue>) -> Rc<AbstractValue> {
        match (&self.expression, &other.expression) {
            // [0 - other] -> -other
            (Expression::CompileTimeConstant(ConstantDomain::I128(0)), _)
            | (Expression::CompileTimeConstant(ConstantDomain::U128(0)), _) => {
                return other.negate();
            }
            // [self - 0] -> self
            (_, Expression::CompileTimeConstant(ConstantDomain::I128(0)))
            | (_, Expression::CompileTimeConstant(ConstantDomain::U128(0))) => {
                return self.clone();
            }
            // [self - (- operand)] -> self + operand
            (_, Expression::Neg { operand }) => {
                return self.addition(operand.clone());
            }
            // [(c1 + x) - c2] -> (c1 - c2) + x
            (Expression::Add { left: c1, right: x }, Expression::CompileTimeConstant(..))
                if c1.is_compile_time_constant() =>
            {
                let c1_min_c2 = c1.subtract(other.clone());
                if !c1_min_c2.is_bottom() {
                    return c1_min_c2.addition(x.clone());
                }
            }
            (
                Expression::Cast {
                    operand: left,
                    target_type: ExpressionType::Usize,
                },
                Expression::Cast {
                    operand: right,
                    target_type: ExpressionType::Usize,
                },
            ) => {
                // [(&x[y] as usize) - (&x as usize)] -> y
                if let (
                    Expression::Offset {
                        left: base,
                        right: offset,
                    },
                    Expression::Reference(..),
                ) = (&left.expression, &right.expression)
                {
                    if base.eq(right) {
                        return offset.clone();
                    }
                }
                // [(expr[y] as usize) - (expr as usize)] -> y
                if let (
                    Expression::Variable {
                        path: left_path,
                        var_type: ExpressionType::ThinPointer,
                    },
                    Expression::Variable {
                        path: right_path,
                        var_type: ExpressionType::ThinPointer,
                    },
                ) = (&left.expression, &right.expression)
                {
                    if let PathEnum::Offset { value } = &left_path.value {
                        if let Expression::Offset {
                            left: base,
                            right: offset,
                        } = &value.expression
                        {
                            if let PathEnum::Computed { value: rv }
                            | PathEnum::HeapBlock { value: rv }
                            | PathEnum::Offset { value: rv } = &right_path.value
                            {
                                if rv.eq(base) {
                                    return offset.clone();
                                }
                            }
                        }
                    }
                }
            }
            _ => {
                // [x - x] -> 0 if x is an integer
                if self.eq(&other) {
                    let t = self.expression.infer_type();
                    if t.is_unsigned_integer() {
                        return Rc::new(ConstantDomain::U128(0).into());
                    } else if t.is_signed_integer() {
                        return Rc::new(ConstantDomain::I128(0).into());
                    }
                }
            }
        }
        self.try_to_constant_fold_and_distribute_binary_op(
            other,
            ConstantDomain::sub,
            Self::subtract,
            |l, r| AbstractValue::make_binary(l, r, |left, right| Expression::Sub { left, right }),
        )
    }

    /// Returns an element that is true if "self - other" is not in range of target_type.
    #[logfn_inputs(TRACE)]
    fn sub_overflows(
        &self,
        other: Rc<AbstractValue>,
        target_type: ExpressionType,
    ) -> Rc<AbstractValue> {
        if self.is_bottom() || self.is_top() || other.is_bottom() || other.is_top() {
            return AbstractValue::make_typed_unknown(
                ExpressionType::Bool,
                Path::new_computed(TOP.into()),
            );
        }
        let interval = self.get_cached_interval().sub(&other.get_cached_interval());
        if interval.is_contained_in(target_type) {
            return Rc::new(FALSE);
        }
        self.try_to_constant_fold_and_distribute_typed_binary_op(
            other,
            target_type,
            ConstantDomain::sub_overflows,
            Self::sub_overflows,
            |l, r, t| {
                AbstractValue::make_typed_binary(l, r, t, |left, right, result_type| {
                    Expression::SubOverflows {
                        left,
                        right,
                        result_type,
                    }
                })
            },
        )
    }

    /// True if all of the concrete values that correspond to self also correspond to other.
    /// Note: !x.subset(y) does not imply y.subset(x).
    #[logfn_inputs(TRACE)]
    fn subset(&self, other: &Rc<AbstractValue>) -> bool {
        if self.expression.eq(&other.expression) {
            return true;
        }
        match (&self.expression, &other.expression) {
            // The empty set is a subset of every other set.
            (Expression::Bottom, _) => true,
            // A non empty set is not a subset of the empty set.
            (_, Expression::Bottom) => false,
            // Every set is a subset of the universal set.
            (_, Expression::Top) => true,
            // The universal set is not a subset of any set other than the universal set.
            (Expression::Top, _) => false,
            // (condition ? consequent : alternate) is a subset of x if both consequent and alternate are subsets of x.
            (
                Expression::ConditionalExpression {
                    consequent,
                    alternate,
                    ..
                },
                _,
            ) => {
                // This is a conservative answer. False does not imply other.subset(self).
                consequent.subset(other) && alternate.subset(other)
            }
            // x is a subset of (condition ? consequent : alternate) if x is a subset of consequent or alternate.
            (
                _,
                Expression::ConditionalExpression {
                    consequent,
                    alternate,
                    ..
                },
            ) => {
                // This is a conservative answer. False does not imply other.subset(self).
                self.subset(consequent) || self.subset(alternate)
            }
            // widen { x } subset widen { z } if x subset z
            (
                Expression::WidenedJoin { operand: o1, .. },
                Expression::WidenedJoin { operand: o2, .. },
            ) => o1.subset(o2),
            // x subset widen { z } if x subset z
            (_, Expression::WidenedJoin { operand, .. }) => {
                // This is a conservative answer. False does not imply other.subset(self).
                self.subset(operand)
            }
            // (left join right) is a subset of x if both left and right are subsets of x.
            (Expression::Join { left, right, .. }, _) => {
                // This is a conservative answer. False does not imply other.subset(self).
                left.subset(other) && right.subset(other)
            }
            // x is a subset of (left join right) if x is a subset of either left or right.
            (_, Expression::Join { left, right, .. }) => {
                // This is a conservative answer. False does not imply other.subset(self).
                self.subset(left) && self.subset(right)
            }
            _ => false,
        }
    }

    /// Constructs a switch value.
    #[logfn_inputs(TRACE)]
    fn switch(
        &self,
        mut cases: Vec<(Rc<AbstractValue>, Rc<AbstractValue>)>,
        default: Rc<AbstractValue>,
    ) -> Rc<AbstractValue> {
        if self.is_compile_time_constant()
            && cases
                .iter()
                .all(|(case_val, _)| case_val.is_compile_time_constant())
        {
            return if let Some((_, case_result)) = cases.iter().find(|(case_val, _)| {
                self.equals(case_val.clone())
                    .as_bool_if_known()
                    .unwrap_or(false)
            }) {
                case_result.clone()
            } else {
                default
            };
        }
        if self.is_top() {
            // No type or path information for the discriminator means we know nothing.
            return AbstractValue::make_typed_unknown(
                default.expression.infer_type(),
                Path::new_computed(Rc::new(TOP)),
            );
        }

        if let Expression::Switch {
            discriminator,
            cases: default_cases,
            default: default_default,
        } = &default.expression
        {
            if self.eq(discriminator) {
                cases.append(&mut default_cases.clone());
                return self.switch(cases, default_default.clone());
            }
        }
        let expression_size = self
            .expression_size
            .wrapping_add(default.expression_size)
            .wrapping_add(cases.iter().fold(0u64, |acc, (x, y)| {
                acc.wrapping_add(x.expression_size)
                    .wrapping_add(y.expression_size)
            }));
        AbstractValue::make_from(
            Expression::Switch {
                discriminator: self.clone(),
                cases,
                default,
            },
            expression_size,
        )
    }

    // Attempts to construct an equivalent expression to self, but with the difference that
    // the type inferred for the resulting expression will be the target type.
    // If this is not possible, the original expression is returned.
    // The need for this function arises from the difficulty of correctly typing variables that have
    // generic types when constructed, but then leak out to caller contexts via summaries.
    #[logfn_inputs(TRACE)]
    fn try_to_retype_as(&self, target_type: ExpressionType) -> Rc<AbstractValue> {
        match &self.expression {
            Expression::Add { left, right } => left
                .try_to_retype_as(target_type)
                .addition(right.try_to_retype_as(target_type)),
            Expression::BitAnd { left, right } => left
                .try_to_retype_as(target_type)
                .bit_and(right.try_to_retype_as(target_type)),
            Expression::BitOr { left, right } => left
                .try_to_retype_as(target_type)
                .bit_or(right.try_to_retype_as(target_type)),
            Expression::BitXor { left, right } => left
                .try_to_retype_as(target_type)
                .bit_xor(right.try_to_retype_as(target_type)),
            Expression::Cast {
                operand,
                target_type: tt,
            } if *tt == ExpressionType::NonPrimitive || *tt == ExpressionType::ThinPointer => {
                operand.try_to_retype_as(target_type)
            }
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => {
                let consequent = consequent.try_to_retype_as(target_type);
                let alternate = alternate.try_to_retype_as(target_type);
                condition.conditional_expression(consequent, alternate)
            }
            Expression::Div { left, right } => left
                .try_to_retype_as(target_type)
                .divide(right.try_to_retype_as(target_type)),
            Expression::Join { left, right } => left
                .try_to_retype_as(target_type)
                .join(right.try_to_retype_as(target_type)),
            Expression::Mul { left, right } => left
                .try_to_retype_as(target_type)
                .multiply(right.try_to_retype_as(target_type)),
            Expression::Rem { left, right } => left
                .try_to_retype_as(target_type)
                .remainder(right.try_to_retype_as(target_type)),
            Expression::Shl { left, right } => left
                .try_to_retype_as(target_type)
                .shift_left(right.try_to_retype_as(target_type)),
            Expression::Sub { left, right } => left
                .try_to_retype_as(target_type)
                .subtract(right.try_to_retype_as(target_type)),
            Expression::Neg { operand } => operand.try_to_retype_as(target_type).negate(),
            Expression::InitialParameterValue { path, .. } => {
                AbstractValue::make_initial_parameter_value(target_type, path.clone())
            }
            Expression::Switch {
                discriminator,
                cases,
                default,
            } => discriminator.switch(
                cases
                    .iter()
                    .map(|(case_val, result_val)| {
                        (case_val.clone(), result_val.try_to_retype_as(target_type))
                    })
                    .collect(),
                default.try_to_retype_as(target_type),
            ),
            Expression::TaggedExpression { operand, tag } => {
                operand.try_to_retype_as(target_type).add_tag(*tag)
            }
            Expression::Variable { path, .. } => {
                AbstractValue::make_typed_unknown(target_type, path.clone())
            }
            Expression::WidenedJoin { .. } => self.clone(),

            _ => self.clone(),
        }
    }

    /// Tries to simplify operation(self, other) by constant folding or by distribution
    /// the operation over self and/or other.
    /// Returns operation(self, other) if no simplification is possible.
    #[logfn(TRACE)]
    fn try_to_constant_fold_and_distribute_binary_op(
        &self,
        other: Rc<AbstractValue>,
        const_op: fn(&ConstantDomain, &ConstantDomain) -> ConstantDomain,
        recursive_op: fn(&Rc<AbstractValue>, Rc<AbstractValue>) -> Rc<AbstractValue>,
        operation: fn(Rc<AbstractValue>, Rc<AbstractValue>) -> Rc<AbstractValue>,
    ) -> Rc<AbstractValue> {
        match (&self.expression, &other.expression) {
            (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) => {
                let result = const_op(v1, v2);
                if result == ConstantDomain::Bottom {
                    self.try_to_distribute_binary_op(other, recursive_op, operation)
                } else {
                    Rc::new(result.into())
                }
            }
            _ => self.try_to_distribute_binary_op(other, recursive_op, operation),
        }
    }

    /// Tries to simplify operation(self, other, target_type) by constant folding or by distribution
    /// the operation over self and/or other.
    /// Returns operation(self, other, target_type) if no simplification is possible.
    #[logfn(TRACE)]
    fn try_to_constant_fold_and_distribute_typed_binary_op(
        &self,
        other: Rc<AbstractValue>,
        target_type: ExpressionType,
        const_op: fn(&ConstantDomain, &ConstantDomain, ExpressionType) -> ConstantDomain,
        recursive_op: fn(
            &Rc<AbstractValue>,
            Rc<AbstractValue>,
            ExpressionType,
        ) -> Rc<AbstractValue>,
        operation: fn(Rc<AbstractValue>, Rc<AbstractValue>, ExpressionType) -> Rc<AbstractValue>,
    ) -> Rc<AbstractValue> {
        match (&self.expression, &other.expression) {
            (Expression::CompileTimeConstant(v1), Expression::CompileTimeConstant(v2)) => {
                let result = const_op(v1, v2, target_type);
                if result == ConstantDomain::Bottom {
                    self.try_to_distribute_typed_binary_op(
                        other,
                        target_type,
                        recursive_op,
                        operation,
                    )
                } else {
                    Rc::new(result.into())
                }
            }
            _ => {
                self.try_to_distribute_typed_binary_op(other, target_type, recursive_op, operation)
            }
        }
    }

    /// Tries to simplify operation(self, target_type) by constant folding or by distribution
    /// the operation over self and/or other.
    /// Returns operation(self, target_type) if no simplification is possible.
    #[logfn(TRACE)]
    fn try_to_constant_fold_and_distribute_typed_unary_op(
        &self,
        target_type: ExpressionType,
        const_op: fn(&ConstantDomain, ExpressionType) -> ConstantDomain,
        recursive_op: fn(&Rc<AbstractValue>, ExpressionType) -> Rc<AbstractValue>,
        operation: fn(Rc<AbstractValue>, ExpressionType) -> Rc<AbstractValue>,
    ) -> Rc<AbstractValue> {
        if let Expression::CompileTimeConstant(v1) = &self.expression {
            let result = const_op(v1, target_type);
            if result != ConstantDomain::Bottom {
                return Rc::new(result.into());
            }
        };
        self.try_to_distribute_typed_unary_op(target_type, recursive_op, operation)
    }

    /// Tries to simplify operation(self) by constant folding or by distribution
    /// the operation over self and/or other.
    /// Returns operation(self) if no simplification is possible.
    #[logfn(TRACE)]
    fn try_to_constant_fold_and_distribute_unary_op(
        &self,
        const_op: fn(&ConstantDomain) -> ConstantDomain,
        recursive_op: fn(&Rc<AbstractValue>) -> Rc<AbstractValue>,
        operation: fn(Rc<AbstractValue>) -> Rc<AbstractValue>,
    ) -> Rc<AbstractValue> {
        if let Expression::CompileTimeConstant(v1) = &self.expression {
            let result = const_op(v1);
            if result != ConstantDomain::Bottom {
                return Rc::new(result.into());
            }
        };
        self.try_to_distribute_unary_op(recursive_op, operation)
    }

    /// Tries to distribute the operation over self and/or other.
    /// Return operation(self, other) if no simplification is possible.
    #[logfn(TRACE)]
    fn try_to_distribute_binary_op(
        &self,
        other: Rc<AbstractValue>,
        recursive_op: fn(&Rc<AbstractValue>, Rc<AbstractValue>) -> Rc<AbstractValue>,
        operation: fn(Rc<AbstractValue>, Rc<AbstractValue>) -> Rc<AbstractValue>,
    ) -> Rc<AbstractValue> {
        if let ConditionalExpression {
            condition,
            consequent,
            alternate,
        } = &self.expression
        {
            return condition.conditional_expression(
                recursive_op(consequent, other.clone()),
                recursive_op(alternate, other.clone()),
            );
        };
        if let ConditionalExpression {
            condition,
            consequent,
            alternate,
        } = &other.expression
        {
            return condition.conditional_expression(
                recursive_op(self, consequent.clone()),
                recursive_op(self, alternate.clone()),
            );
        };
        if let Join { left, right } = &self.expression {
            return recursive_op(left, other.clone()).join(recursive_op(right, other));
        }
        if let Join { left, right } = &other.expression {
            return recursive_op(self, left.clone()).join(recursive_op(self, right.clone()));
        }
        operation(self.clone(), other)
    }

    /// Tries to distribute the operation over self and/or other.
    /// Return operation(self, other) if no simplification is possible.
    #[logfn(TRACE)]
    fn try_to_distribute_typed_binary_op(
        &self,
        other: Rc<AbstractValue>,
        target_type: ExpressionType,
        recursive_op: fn(
            &Rc<AbstractValue>,
            Rc<AbstractValue>,
            ExpressionType,
        ) -> Rc<AbstractValue>,
        operation: fn(Rc<AbstractValue>, Rc<AbstractValue>, ExpressionType) -> Rc<AbstractValue>,
    ) -> Rc<AbstractValue> {
        if let ConditionalExpression {
            condition,
            consequent,
            alternate,
        } = &self.expression
        {
            return condition.conditional_expression(
                recursive_op(consequent, other.clone(), target_type),
                recursive_op(alternate, other.clone(), target_type),
            );
        };
        if let ConditionalExpression {
            condition,
            consequent,
            alternate,
        } = &other.expression
        {
            return condition.conditional_expression(
                recursive_op(self, consequent.clone(), target_type),
                recursive_op(self, alternate.clone(), target_type),
            );
        };
        if let Join { left, right } = &self.expression {
            return recursive_op(left, other.clone(), target_type).join(recursive_op(
                right,
                other,
                target_type,
            ));
        }
        if let Join { left, right } = &other.expression {
            return recursive_op(self, left.clone(), target_type).join(recursive_op(
                self,
                right.clone(),
                target_type,
            ));
        }
        operation(self.clone(), other, target_type)
    }

    /// Tries to distribute the operation over self and/or other.
    /// Return operation(self, target_type) if no simplification is possible.
    #[logfn(TRACE)]
    fn try_to_distribute_typed_unary_op(
        &self,
        target_type: ExpressionType,
        recursive_op: fn(&Rc<AbstractValue>, ExpressionType) -> Rc<AbstractValue>,
        operation: fn(Rc<AbstractValue>, ExpressionType) -> Rc<AbstractValue>,
    ) -> Rc<AbstractValue> {
        if let ConditionalExpression {
            condition,
            consequent,
            alternate,
        } = &self.expression
        {
            return condition.conditional_expression(
                recursive_op(consequent, target_type),
                recursive_op(alternate, target_type),
            );
        };
        if let Join { left, right } = &self.expression {
            return recursive_op(left, target_type).join(recursive_op(right, target_type));
        }
        operation(self.clone(), target_type)
    }

    /// Tries to distribute the operation over self and/or other.
    /// Return operation(self) if no simplification is possible.
    fn try_to_distribute_unary_op(
        &self,
        recursive_op: fn(&Rc<AbstractValue>) -> Rc<AbstractValue>,
        operation: fn(Rc<AbstractValue>) -> Rc<AbstractValue>,
    ) -> Rc<AbstractValue> {
        if let ConditionalExpression {
            condition,
            consequent,
            alternate,
        } = &self.expression
        {
            return condition
                .conditional_expression(recursive_op(consequent), recursive_op(alternate));
        };
        if let Join { left, right } = &self.expression {
            return recursive_op(left).join(recursive_op(right));
        }
        operation(self.clone())
    }

    /// Gets or constructs an interval that is cached.
    #[logfn_inputs(TRACE)]
    fn get_cached_interval(&self) -> Rc<IntervalDomain> {
        {
            {
                let cached_interval = self.interval.borrow();
                let interval_opt = cached_interval.as_ref();
                if let Some(interval) = interval_opt {
                    return interval.clone();
                }
            }
            let interval = self.get_as_interval();
            {
                let mut cached_interval = self.interval.borrow_mut();
                *cached_interval = Some(Rc::new(interval));
            }
        }
        self.get_cached_interval()
    }

    /// Constructs an element of the Interval domain for simple expressions.
    #[logfn_inputs(TRACE)]
    fn get_as_interval(&self) -> IntervalDomain {
        match &self.expression {
            Expression::Top => interval_domain::BOTTOM,
            Expression::Add { left, right } => left.get_as_interval().add(&right.get_as_interval()),
            Expression::BitAnd { left, .. } => {
                if let Expression::CompileTimeConstant(ConstantDomain::U128(v)) = left.expression {
                    if v < (i128::MAX as u128) && (v + 1).is_power_of_two() {
                        let lower: IntervalDomain = 0u128.into();
                        let upper: IntervalDomain = v.into();
                        return lower.widen(&upper);
                    }
                }
                interval_domain::BOTTOM
            }
            Expression::Cast {
                operand,
                target_type,
            } => operand
                .get_as_interval()
                .intersect(&IntervalDomain::from(*target_type)),
            Expression::CompileTimeConstant(ConstantDomain::I128(val)) => (*val).into(),
            Expression::CompileTimeConstant(ConstantDomain::U128(val)) => (*val).into(),
            Expression::ConditionalExpression {
                consequent,
                alternate,
                ..
            } => consequent
                .get_as_interval()
                .widen(&alternate.get_as_interval()),
            Expression::IntrinsicBitVectorUnary {
                name, bit_length, ..
            } => match name {
                KnownNames::StdIntrinsicsCtlz
                | KnownNames::StdIntrinsicsCtlzNonzero
                | KnownNames::StdIntrinsicsCtpop
                | KnownNames::StdIntrinsicsCttz
                | KnownNames::StdIntrinsicsCttzNonzero => {
                    let min_value: IntervalDomain = IntervalDomain::from(0u128);
                    let max_value = IntervalDomain::from(*bit_length as u128);
                    min_value.widen(&max_value)
                }
                _ => interval_domain::BOTTOM,
            },
            Expression::Join { left, right, .. } => {
                left.get_as_interval().widen(&right.get_as_interval())
            }
            Expression::Mul { left, right } => left.get_as_interval().mul(&right.get_as_interval()),
            Expression::Neg { operand } => operand.get_as_interval().neg(),
            Expression::Sub { left, right } => left.get_as_interval().sub(&right.get_as_interval()),
            Expression::Switch { cases, default, .. } => cases
                .iter()
                .fold(default.get_as_interval(), |acc, (_, result)| {
                    acc.widen(&result.get_as_interval())
                }),
            Expression::TaggedExpression { operand, .. } => operand.get_as_interval(),
            Expression::WidenedJoin { operand, .. } => {
                let interval = operand.get_as_interval();
                if interval.is_bottom() {
                    return interval;
                }
                if let Expression::Join { left, .. } = &operand.expression {
                    let left_interval = left.get_as_interval();
                    if left_interval.is_bottom() {
                        return interval_domain::BOTTOM;
                    }
                    match (left_interval.lower_bound(), interval.lower_bound()) {
                        (Some(llb), Some(lb)) if llb == lb => {
                            // The lower bound is finite and does not change as a result of the fixed
                            // point computation, so we can keep it, but we remove the upper bound.
                            return interval.remove_upper_bound();
                        }
                        _ => (),
                    }
                    match (left_interval.upper_bound(), interval.upper_bound()) {
                        (Some(lub), Some(ub)) if lub == ub => {
                            // The upper bound is finite and does not change as a result of the fixed
                            // point computation, so we can keep it, but we remove the lower bound.
                            return interval.remove_lower_bound();
                        }
                        _ => (),
                    }
                }
                interval
            }
            _ => interval_domain::BOTTOM,
        }
    }

    /// Determines if the expression is known at compile time to always be a non-null pointer.
    #[logfn_inputs(TRACE)]
    fn get_is_non_null(&self) -> bool {
        match &self.expression {
            Expression::ConditionalExpression {
                consequent,
                alternate,
                ..
            } => consequent.is_non_null() && alternate.is_non_null(),
            Expression::Join { left, right, .. } => left.is_non_null() && right.is_non_null(),
            Expression::Offset { left, .. } => left.is_non_null(),
            Expression::Reference(..) => true,
            Expression::WidenedJoin { operand, .. } => operand.is_non_null(),
            _ => false,
        }
    }

    /// Gets or constructs a tag domain element that is cached.
    #[logfn_inputs(TRACE)]
    fn get_cached_tags(&self) -> Rc<TagDomain> {
        {
            let mut cached_tags = self.tags.borrow_mut();
            let tags_opt = cached_tags.as_ref();
            if let Some(tags) = tags_opt {
                return tags.clone();
            }
            let tags = self.get_tags();
            *cached_tags = Some(Rc::new(tags));
        }
        self.get_cached_tags()
    }

    /// Constructs an element of the tag domain for simple expressions.
    #[logfn_inputs(TRACE)]
    fn get_tags(&self) -> TagDomain {
        let exp_tag_prop_opt = self.expression.get_tag_propagation();

        // First deal with expressions that do not propagate tags or have special propagation behavior.
        match &self.expression {
            Expression::Top
            | Expression::Bottom
            | Expression::CompileTimeConstant { .. }
            | Expression::HeapBlock { .. }
            | Expression::HeapBlockLayout { .. }
            | Expression::Reference { .. }
            | Expression::UnknownTagCheck { .. } => return TagDomain::empty_set(),

            Expression::InitialParameterValue { .. }
            | Expression::UnknownModelField { .. }
            | Expression::UnknownTagField { .. }
            | Expression::Variable { .. } => {
                // A variable is an unknown value of a place in memory.
                // Therefore, the associated tags are also unknown.
                return TagDomain::top();
            }

            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => {
                // For each tag A, whether the conditional expression has tag A or not is
                // (condition has tag A) or ((consequent has tag A) join (alternate has tag A)).
                return condition.get_cached_tags().or(&consequent
                    .get_cached_tags()
                    .join(&alternate.get_cached_tags()));
            }

            Expression::Join { left, right, .. } => {
                // For each tag A, whether the join expression has tag A or not is
                // ((left has tag A) join (right has tag A)).
                return left
                    .get_cached_tags()
                    .join(right.get_cached_tags().as_ref());
            }

            Expression::Switch {
                discriminator,
                cases,
                default,
            } => {
                // For each tag A, whether the switch expression has tag A or not is
                // (discriminator has tag A) or ((case_0 has tag A) join .. join (case_n has tag A) join (default has tag A)).
                let mut tags_from_cases = (*default.get_cached_tags()).clone();
                for case in cases {
                    tags_from_cases = tags_from_cases.join(case.1.get_cached_tags().as_ref())
                }
                return discriminator.get_cached_tags().or(&tags_from_cases);
            }

            Expression::TaggedExpression { operand, tag } => {
                return operand.get_cached_tags().add_tag(*tag);
            }

            Expression::WidenedJoin { operand, .. } => {
                let tags = operand.get_cached_tags();
                return (*tags).clone();
            }

            _ => {
                verify!(exp_tag_prop_opt.is_some());
            }
        }

        let exp_tag_prop = exp_tag_prop_opt.unwrap();

        // Then deal with expressions that have standard propagation behavior, i.e., taking tags
        // from children nodes.
        match &self.expression {
            Expression::Add { left, right }
            | Expression::AddOverflows { left, right, .. }
            | Expression::And { left, right }
            | Expression::BitAnd { left, right }
            | Expression::BitOr { left, right }
            | Expression::BitXor { left, right }
            | Expression::Div { left, right }
            | Expression::Equals { left, right }
            | Expression::GreaterOrEqual { left, right }
            | Expression::GreaterThan { left, right }
            | Expression::IntrinsicBinary { left, right, .. }
            | Expression::LessOrEqual { left, right }
            | Expression::LessThan { left, right }
            | Expression::Mul { left, right }
            | Expression::MulOverflows { left, right, .. }
            | Expression::Ne { left, right }
            | Expression::Or { left, right }
            | Expression::Offset { left, right }
            | Expression::Rem { left, right }
            | Expression::Shl { left, right }
            | Expression::ShlOverflows { left, right, .. }
            | Expression::Shr { left, right, .. }
            | Expression::ShrOverflows { left, right, .. }
            | Expression::Sub { left, right }
            | Expression::SubOverflows { left, right, .. } => left
                .get_cached_tags()
                .propagate_through(exp_tag_prop)
                .or(&right.get_cached_tags().propagate_through(exp_tag_prop)),

            Expression::BitNot { operand, .. }
            | Expression::Cast { operand, .. }
            | Expression::IntrinsicBitVectorUnary { operand, .. }
            | Expression::IntrinsicFloatingPointUnary { operand, .. }
            | Expression::LogicalNot { operand, .. }
            | Expression::Neg { operand, .. }
            | Expression::Transmute { operand, .. } => {
                operand.get_cached_tags().propagate_through(exp_tag_prop)
            }

            Expression::Memcmp {
                left,
                right,
                length,
            } => left
                .get_cached_tags()
                .propagate_through(exp_tag_prop)
                .or(&right.get_cached_tags().propagate_through(exp_tag_prop))
                .or(&length.get_cached_tags().propagate_through(exp_tag_prop)),

            Expression::UninterpretedCall {
                callee, arguments, ..
            } => {
                let mut tags = callee.get_cached_tags().propagate_through(exp_tag_prop);
                for argument in arguments {
                    tags = tags.or(&argument.get_cached_tags().propagate_through(exp_tag_prop))
                }
                tags
            }

            _ => {
                verify_unreachable!();
            }
        }
    }

    /// Returns a subexpression that is a widened expression.
    /// Returns None if no such expression can be found.
    #[logfn_inputs(TRACE)]
    fn get_widened_subexpression(&self, path: &Rc<Path>) -> Option<Rc<AbstractValue>> {
        match &self.expression {
            Expression::Bottom | Expression::Top => None,
            Expression::Add { left, right }
            | Expression::AddOverflows { left, right, .. }
            | Expression::And { left, right }
            | Expression::BitAnd { left, right }
            | Expression::BitOr { left, right }
            | Expression::BitXor { left, right }
            | Expression::Div { left, right }
            | Expression::Equals { left, right }
            | Expression::GreaterOrEqual { left, right }
            | Expression::GreaterThan { left, right }
            | Expression::IntrinsicBinary { left, right, .. }
            | Expression::Join { left, right, .. }
            | Expression::LessOrEqual { left, right }
            | Expression::LessThan { left, right }
            | Expression::Mul { left, right }
            | Expression::MulOverflows { left, right, .. }
            | Expression::Ne { left, right }
            | Expression::Offset { left, right }
            | Expression::Or { left, right }
            | Expression::Rem { left, right }
            | Expression::Shl { left, right }
            | Expression::ShlOverflows { left, right, .. }
            | Expression::Shr { left, right, .. }
            | Expression::ShrOverflows { left, right, .. }
            | Expression::Sub { left, right }
            | Expression::SubOverflows { left, right, .. } => left
                .get_widened_subexpression(path)
                .or_else(|| right.get_widened_subexpression(path)),
            Expression::BitNot { operand, .. }
            | Expression::Cast { operand, .. }
            | Expression::IntrinsicBitVectorUnary { operand, .. }
            | Expression::IntrinsicFloatingPointUnary { operand, .. }
            | Expression::Neg { operand }
            | Expression::LogicalNot { operand }
            | Expression::TaggedExpression { operand, .. }
            | Expression::Transmute { operand, .. }
            | Expression::UnknownTagCheck { operand, .. } => {
                operand.get_widened_subexpression(path)
            }
            Expression::CompileTimeConstant(..) => None,
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => condition.get_widened_subexpression(path).or_else(|| {
                consequent
                    .get_widened_subexpression(path)
                    .or_else(|| alternate.get_widened_subexpression(path))
            }),
            Expression::HeapBlock { .. } => None,
            Expression::HeapBlockLayout {
                length, alignment, ..
            } => length
                .get_widened_subexpression(path)
                .or_else(|| alignment.get_widened_subexpression(path)),
            Expression::Memcmp {
                left,
                right,
                length,
            } => left.get_widened_subexpression(path).or_else(|| {
                right
                    .get_widened_subexpression(path)
                    .or_else(|| length.get_widened_subexpression(path))
            }),
            Expression::Reference(..) => None,
            Expression::InitialParameterValue { .. } => None,
            Expression::Switch {
                discriminator,
                cases,
                default,
            } => discriminator.get_widened_subexpression(path).or_else(|| {
                default.get_widened_subexpression(path).or_else(|| {
                    cases.iter().find_map(|(case_val, result_val)| {
                        case_val
                            .get_widened_subexpression(path)
                            .or_else(|| result_val.get_widened_subexpression(path))
                    })
                })
            }),
            Expression::UninterpretedCall {
                callee,
                arguments: args,
                ..
            } => callee.get_widened_subexpression(path).or_else(|| {
                args.iter()
                    .find_map(|arg| arg.get_widened_subexpression(path))
            }),
            Expression::UnknownModelField { .. } => None,
            Expression::UnknownTagField { .. } => None,
            Expression::Variable { .. } => None,
            Expression::WidenedJoin { path: p, .. } => {
                if p.eq(path) {
                    Some(self.clone())
                } else {
                    None
                }
            }
        }
    }

    /// Returns a value that is simplified (refined) by replacing parameter values
    /// with their corresponding argument values. If no refinement is possible
    /// the result is simply a clone of this value.
    #[logfn_inputs(TRACE)]
    fn refine_parameters_and_paths(
        &self,
        args: &[(Rc<Path>, Rc<AbstractValue>)],
        result: &Option<Rc<Path>>,
        pre_env: &Environment,
        post_env: &Environment,
        // An offset to add to locals from the called function so that they do not clash with caller locals.
        fresh: usize,
    ) -> Rc<AbstractValue> {
        match &self.expression {
            Expression::Bottom | Expression::Top => self.clone(),
            Expression::Add { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .addition(
                    right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                ),
            Expression::AddOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .add_overflows(
                    right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                    *result_type,
                ),
            Expression::And { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .and(right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh)),
            Expression::BitAnd { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .bit_and(right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh)),
            Expression::BitNot {
                operand,
                result_type,
            } => operand
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .bit_not(*result_type),
            Expression::BitOr { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .bit_or(right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh)),
            Expression::BitXor { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .bit_xor(right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh)),
            Expression::Cast {
                operand,
                target_type,
            } => operand
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .cast(*target_type),
            Expression::CompileTimeConstant(..) => self.clone(),
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => {
                let mut cond =
                    condition.refine_parameters_and_paths(args, result, pre_env, post_env, fresh);
                if let Some(c) = cond.as_bool_if_known() {
                    if c {
                        consequent
                            .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                    } else {
                        alternate
                            .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                    }
                } else {
                    if condition.expression.contains_local_variable(false) {
                        // The condition contains local state of the callee and could not be
                        // satisfied by refining other parts of the condition with call site state.
                        if let Some(promotable_condition) = cond.extract_promotable_disjuncts(false)
                        {
                            // The overall condition can be satisfied by our caller
                            // so simplify the condition to just that part.
                            cond = promotable_condition;
                        } else {
                            // The condition can not be satisfied without knowing the callee state
                            // so just join (and thus avoid keeping around a potentially large useless expression).
                            return consequent
                                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                                .join(alternate.refine_parameters_and_paths(
                                    args, result, pre_env, post_env, fresh,
                                ));
                        }
                    }
                    cond.conditional_expression(
                        consequent
                            .refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                        alternate
                            .refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                    )
                }
            }
            Expression::Div { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .divide(right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh)),
            Expression::Equals { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .equals(right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh)),
            Expression::GreaterOrEqual { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .greater_or_equal(
                    right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                ),
            Expression::GreaterThan { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .greater_than(
                    right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                ),
            Expression::HeapBlock {
                abstract_address,
                is_zeroed,
            } => AbstractValue::make_from(
                Expression::HeapBlock {
                    abstract_address: *abstract_address + fresh,
                    is_zeroed: *is_zeroed,
                },
                1,
            ),
            Expression::HeapBlockLayout {
                length,
                alignment,
                source,
            } => AbstractValue::make_from(
                Expression::HeapBlockLayout {
                    length: length
                        .refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                    alignment: alignment
                        .refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                    source: *source,
                },
                1,
            ),
            Expression::InitialParameterValue { path, var_type } => {
                let refined_path =
                    path.refine_parameters_and_paths(args, result, pre_env, pre_env, fresh);
                if let PathEnum::Computed { value } | PathEnum::Offset { value } =
                    &refined_path.value
                {
                    return value.clone();
                } else if let Some(val) = pre_env.value_at(&refined_path) {
                    return val.clone();
                }
                // If the path does not have a known value in the pre environment, make an unknown
                // value. If the path is still rooted in parameter make sure that it does not get
                // affected by subsequent side effects on the parameter.
                if refined_path.is_rooted_by_parameter() {
                    // This will not get refined again
                    AbstractValue::make_initial_parameter_value(*var_type, refined_path)
                } else {
                    // The value is rooted in a local variable leaked from the callee or
                    // in a static. In the latter case we want lookup_and_refine_value to
                    // to see this. In the former, refinement is a no-op.
                    AbstractValue::make_typed_unknown(*var_type, refined_path)
                }
            }
            Expression::IntrinsicBinary { left, right, name } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .intrinsic_binary(
                    right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                    *name,
                ),
            Expression::IntrinsicBitVectorUnary {
                operand,
                bit_length,
                name,
            } => operand
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .intrinsic_bit_vector_unary(*bit_length, *name),
            Expression::IntrinsicFloatingPointUnary { operand, name } => operand
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .intrinsic_floating_point_unary(*name),
            Expression::Join { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .join(right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh)),
            Expression::LessOrEqual { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .less_or_equal(
                    right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                ),
            Expression::LessThan { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .less_than(
                    right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                ),
            Expression::LogicalNot { operand } => operand
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .logical_not(),
            Expression::Memcmp {
                left,
                right,
                length,
            } => {
                let refined_left =
                    left.refine_parameters_and_paths(args, result, pre_env, post_env, fresh);
                let refined_right =
                    right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh);
                let refined_length =
                    length.refine_parameters_and_paths(args, result, pre_env, post_env, fresh);

                if let Expression::CompileTimeConstant(ConstantDomain::U128(len)) =
                    &refined_length.expression
                {
                    let n = *len as usize;

                    let arr1 = refined_left.try_resolve_as_byte_array(post_env);
                    let arr2 = refined_right.try_resolve_as_byte_array(post_env);
                    if let (Some(arr1), Some(arr2)) = (&arr1, &arr2) {
                        let n1 = usize::min(n, arr1.len());
                        let n2 = usize::min(n, arr2.len());
                        return Rc::new(
                            ConstantDomain::I128(arr1[..n1].cmp(&arr2[..n2]) as i32 as i128).into(),
                        );
                    }

                    let str1 = refined_left.try_resolve_as_ref_to_str(post_env);
                    let str2 = refined_right.try_resolve_as_ref_to_str(post_env);
                    if let (Some(str1), Some(str2)) = (str1, str2) {
                        let n1 = usize::min(n, str1.len());
                        let n2 = usize::min(n, str2.len());
                        return Rc::new(
                            ConstantDomain::I128(str1[..n1].cmp(&str2[..n2]) as i32 as i128).into(),
                        );
                    }
                }
                AbstractValue::make_memcmp(refined_left, refined_right, refined_length)
            }
            Expression::Mul { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .multiply(
                    right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                ),
            Expression::MulOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .mul_overflows(
                    right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                    *result_type,
                ),
            Expression::Ne { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .not_equals(
                    right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                ),
            Expression::Neg { operand } => operand
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .negate(),
            Expression::Offset { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .offset(right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh)),
            Expression::Or { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .or(right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh)),
            Expression::Reference(path) => {
                // if the path is a parameter, the reference is an artifact of its type
                // and needs to be removed in the call context
                match &path.value {
                    PathEnum::Parameter { ordinal } => {
                        if *ordinal > args.len() {
                            warn!("Summary refers to a parameter that does not have a matching argument");
                            Rc::new(BOTTOM)
                        } else {
                            args[*ordinal - 1].1.clone()
                        }
                    }
                    _ => {
                        let refined_path = path
                            .refine_parameters_and_paths(args, result, pre_env, post_env, fresh);
                        AbstractValue::make_reference(refined_path)
                    }
                }
            }
            Expression::Rem { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .remainder(
                    right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                ),
            Expression::Shl { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .shift_left(
                    right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                ),
            Expression::ShlOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .shl_overflows(
                    right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                    *result_type,
                ),
            Expression::Shr { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .shr(right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh)),
            Expression::ShrOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .shr_overflows(
                    right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                    *result_type,
                ),
            Expression::Sub { left, right } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .subtract(
                    right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                ),
            Expression::SubOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .sub_overflows(
                    right.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                    *result_type,
                ),
            Expression::Switch {
                discriminator,
                cases,
                default,
            } => discriminator
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .switch(
                    cases
                        .iter()
                        .map(|(case_val, result_val)| {
                            (
                                case_val.refine_parameters_and_paths(
                                    args, result, pre_env, post_env, fresh,
                                ),
                                result_val.refine_parameters_and_paths(
                                    args, result, pre_env, post_env, fresh,
                                ),
                            )
                        })
                        .collect(),
                    default.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                ),
            Expression::TaggedExpression { operand, tag } => operand
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .add_tag(*tag),
            Expression::Transmute {
                operand,
                target_type,
            } => operand
                .refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                .transmute(*target_type),
            Expression::UninterpretedCall {
                callee,
                arguments,
                result_type,
                path,
            } => {
                let refined_callee =
                    callee.refine_parameters_and_paths(args, result, pre_env, post_env, fresh);
                let refined_arguments = arguments
                    .iter()
                    .map(|arg| {
                        arg.refine_parameters_and_paths(args, result, pre_env, post_env, fresh)
                    })
                    .collect();
                let refined_path =
                    path.refine_parameters_and_paths(args, result, pre_env, post_env, fresh);
                refined_callee.uninterpreted_call(refined_arguments, *result_type, refined_path)
            }
            Expression::UnknownModelField { path, default } => {
                let refined_path =
                    path.refine_parameters_and_paths(args, result, pre_env, post_env, fresh);
                if !matches!(&refined_path.value, PathEnum::Computed { .. }) {
                    if let Some(val) = post_env.value_at(&refined_path) {
                        // This environment has a value for the model field.
                        val.clone()
                    } else if refined_path.is_rooted_by_parameter() {
                        // Keep passing the buck to the next caller.
                        AbstractValue::make_from(
                            Expression::UnknownModelField {
                                path: refined_path,
                                default: default.clone(),
                            },
                            default.expression_size.saturating_add(1),
                        )
                    } else {
                        // The buck stops here and the environment does not have a value for model field.
                        default.clone()
                    }
                } else {
                    AbstractValue::make_from(
                        Expression::UnknownModelField {
                            path: refined_path,
                            default: default.clone(),
                        },
                        1,
                    )
                }
            }
            Expression::UnknownTagCheck {
                operand,
                tag,
                checking_presence,
            } => AbstractValue::make_tag_check(
                operand.refine_parameters_and_paths(args, result, pre_env, post_env, fresh),
                *tag,
                *checking_presence,
            ),
            Expression::UnknownTagField { path } => {
                let refined_path =
                    path.refine_parameters_and_paths(args, result, pre_env, post_env, fresh);
                if !matches!(&refined_path.value, PathEnum::Computed { .. }) {
                    if let Some(val) = post_env.value_at(&refined_path) {
                        // This environment has a value for the tag field.
                        val.clone()
                    } else if !refined_path.is_rooted_by_parameter() {
                        // Return the dummy untagged value if refined_path is not rooted by a function parameter.
                        Rc::new(DUMMY_UNTAGGED_VALUE)
                    } else {
                        // Otherwise, return again an unknown tag field.
                        AbstractValue::make_from(
                            Expression::UnknownTagField { path: refined_path },
                            1,
                        )
                    }
                } else {
                    AbstractValue::make_from(Expression::UnknownTagField { path: refined_path }, 1)
                }
            }
            Expression::Variable { path, var_type } => {
                let refined_path =
                    path.refine_parameters_and_paths(args, result, pre_env, post_env, fresh);
                if let PathEnum::Computed { value }
                | PathEnum::HeapBlock { value }
                | PathEnum::Offset { value } = &refined_path.value
                {
                    value.clone()
                } else if let Some(val) = post_env.value_at(&refined_path) {
                    val.clone()
                } else if refined_path.eq(path) {
                    self.clone()
                } else {
                    AbstractValue::make_typed_unknown(*var_type, refined_path)
                }
            }
            Expression::WidenedJoin { path, operand } => {
                let refined_path =
                    path.refine_parameters_and_paths(args, result, pre_env, post_env, fresh);
                let refined_operand =
                    operand.refine_parameters_and_paths(args, result, pre_env, post_env, fresh);
                if matches!(refined_operand.expression, Expression::Join { .. }) {
                    refined_operand.widen(&refined_path)
                } else {
                    AbstractValue::make_typed_unknown(
                        refined_operand.expression.infer_type(),
                        refined_path,
                    )
                }
            }
        }
    }

    /// Returns a domain that is simplified (refined) by using the current path conditions
    /// (conditions known to be true in the current context). If no refinement is possible
    /// the result is simply a clone of this domain.
    ///
    /// This function is performance critical and involves a tricky trade-off: Invoking it
    /// is expensive, particularly when expressions get large (hence k_limits::MAX_EXPRESSION_SIZE).
    /// One reason for this is that expressions are traversed without doing any kind of occurs check,
    /// so expressions that are not large in memory usage (because of sharing) can still be too large
    /// to traverse. Currently there is no really efficient way to add an occurs check, so the
    /// k-limit approach is cheaper, at the cost of losing precision.
    ///
    /// On the other hand, getting rid of this refinement (and the k-limits it needs) will cause
    /// a lot of expressions to get much larger because of joining and composing. This will increase
    /// the cost of refine_parameters, which is essential. Likewise, it wil also increase the cost
    /// of refine_paths, which ensures that paths stay unique (dealing with aliasing is expensive).
    #[logfn_inputs(TRACE)]
    fn refine_with(&self, path_condition: &Self, depth: usize) -> Rc<AbstractValue> {
        if self.is_bottom() || self.is_top() {
            return self.clone();
        };
        //do not use false path conditions to refine things
        checked_precondition!(path_condition.as_bool_if_known().is_none());
        if depth >= k_limits::MAX_REFINE_DEPTH {
            trace!("max refine depth exceeded during refine_with");
            return self.clone();
        }
        // In this context path_condition is true
        if path_condition.eq(self) {
            return Rc::new(TRUE);
        }

        // If the path context constrains the self expression to be equal to a constant, just
        // return the constant.
        if let Expression::Equals { left, right } = &path_condition.expression {
            if let Expression::CompileTimeConstant(..) = &left.expression {
                if self.eq(right) {
                    return left.clone();
                }
            }
            if let Expression::CompileTimeConstant(..) = &right.expression {
                if self.eq(left) {
                    return right.clone();
                }
            }
        }
        // Traverse the self expression, looking for recursive refinement opportunities.
        // Important, keep the traversal as trivial as possible and put optimizations in
        // the transfer functions. Also, keep the transfer functions constant in cost as
        // much as possible. Any time they are not, this function becomes quadratic and
        // performance becomes terrible.
        match &self.expression {
            Expression::Bottom | Expression::Top => self.clone(),
            Expression::Add { left, right } => left
                .refine_with(path_condition, depth + 1)
                .addition(right.refine_with(path_condition, depth + 1)),
            Expression::AddOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_with(path_condition, depth + 1)
                .add_overflows(right.refine_with(path_condition, depth + 1), *result_type),
            Expression::And { left, right } => left
                .refine_with(path_condition, depth + 1)
                .and(right.refine_with(path_condition, depth + 1)),
            Expression::BitAnd { left, right } => left
                .refine_with(path_condition, depth + 1)
                .bit_and(right.refine_with(path_condition, depth + 1)),
            Expression::BitNot {
                operand,
                result_type,
            } => operand
                .refine_with(path_condition, depth + 1)
                .bit_not(*result_type),
            Expression::BitOr { left, right } => left
                .refine_with(path_condition, depth + 1)
                .bit_or(right.refine_with(path_condition, depth + 1)),
            Expression::BitXor { left, right } => left
                .refine_with(path_condition, depth + 1)
                .bit_xor(right.refine_with(path_condition, depth + 1)),
            Expression::Cast {
                operand,
                target_type,
            } => operand
                .refine_with(path_condition, depth + 1)
                .cast(*target_type),
            Expression::CompileTimeConstant(..) => self.clone(),
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => {
                // The implies checks should be redundant, but currently help with precision
                // presumably because they are not k-limited like the refinement of the path
                // condition. They might also help with performance because they avoid
                // two refinements and the expensive and constructor, if they succeed.
                // If they mostly fail, they will cost more than they save. It is not
                // clear at this point if they are a win, but they are kept for the sake of precision.
                if path_condition.implies(condition) {
                    consequent.refine_with(path_condition, depth + 1)
                } else if path_condition.implies_not(condition) {
                    alternate.refine_with(path_condition, depth + 1)
                } else {
                    let refined_condition = condition.refine_with(path_condition, depth + 1);
                    let refined_condition_as_bool = refined_condition.as_bool_if_known();
                    let refined_consequent = consequent.refine_with(path_condition, depth + 1);
                    if refined_condition_as_bool.unwrap_or(false) {
                        return refined_consequent;
                    }
                    let refined_alternate = alternate.refine_with(path_condition, depth + 1);
                    if !refined_condition_as_bool.unwrap_or(true) {
                        return refined_alternate;
                    }
                    refined_condition.conditional_expression(refined_consequent, refined_alternate)
                }
            }
            Expression::Div { left, right } => left
                .refine_with(path_condition, depth + 1)
                .divide(right.refine_with(path_condition, depth + 1)),
            Expression::Equals { left, right } => left
                .refine_with(path_condition, depth + 1)
                .equals(right.refine_with(path_condition, depth + 1)),
            Expression::GreaterOrEqual { left, right } => left
                .refine_with(path_condition, depth + 1)
                .greater_or_equal(right.refine_with(path_condition, depth + 1)),
            Expression::GreaterThan { left, right } => left
                .refine_with(path_condition, depth + 1)
                .greater_than(right.refine_with(path_condition, depth + 1)),
            Expression::IntrinsicBinary { left, right, name } => left
                .refine_with(path_condition, depth + 1)
                .intrinsic_binary(right.refine_with(path_condition, depth + 1), *name),
            Expression::IntrinsicBitVectorUnary {
                operand,
                bit_length,
                name,
            } => operand
                .refine_with(path_condition, depth + 1)
                .intrinsic_bit_vector_unary(*bit_length, *name),
            Expression::HeapBlock { .. } => self.clone(),
            Expression::HeapBlockLayout {
                length,
                alignment,
                source,
            } => AbstractValue::make_from(
                Expression::HeapBlockLayout {
                    length: length.refine_with(path_condition, depth + 1),
                    alignment: alignment.refine_with(path_condition, depth + 1),
                    source: *source,
                },
                1,
            ),
            Expression::IntrinsicFloatingPointUnary { operand, name } => operand
                .refine_with(path_condition, depth + 1)
                .intrinsic_floating_point_unary(*name),
            Expression::Join { left, right } => left
                .refine_with(path_condition, depth + 1)
                .join(right.refine_with(path_condition, depth + 1)),
            Expression::LessOrEqual { left, right } => left
                .refine_with(path_condition, depth + 1)
                .less_or_equal(right.refine_with(path_condition, depth + 1)),
            Expression::LessThan { left, right } => left
                .refine_with(path_condition, depth + 1)
                .less_than(right.refine_with(path_condition, depth + 1)),
            Expression::Memcmp {
                left,
                right,
                length,
            } => {
                let refined_length = length.refine_with(path_condition, depth + 1);
                AbstractValue::make_memcmp(left.clone(), right.clone(), refined_length)
            }
            Expression::Mul { left, right } => left
                .refine_with(path_condition, depth + 1)
                .multiply(right.refine_with(path_condition, depth + 1)),
            Expression::MulOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_with(path_condition, depth + 1)
                .mul_overflows(right.refine_with(path_condition, depth + 1), *result_type),
            Expression::Ne { left, right } => left
                .refine_with(path_condition, depth + 1)
                .not_equals(right.refine_with(path_condition, depth + 1)),
            Expression::Neg { operand } => operand.refine_with(path_condition, depth + 1).negate(),
            Expression::LogicalNot { operand } => {
                operand.refine_with(path_condition, depth + 1).logical_not()
            }
            Expression::Offset { left, right } => left
                .refine_with(path_condition, depth + 1)
                .offset(right.refine_with(path_condition, depth + 1)),
            Expression::Or { left, right } => {
                // Ideally the constructor should do the simplifications, but in practice or
                // expressions grow quite large due to composition and it really helps to avoid
                // refining the right expression whenever possible, even at the expense of
                // more checks here. If the performance of implies and implies_not should become
                // significantly worse than it is now, this could become a performance bottle neck.
                if path_condition.implies(left) || path_condition.implies(right) {
                    Rc::new(TRUE)
                } else if path_condition.implies_not(left) {
                    if path_condition.implies_not(right) {
                        Rc::new(FALSE)
                    } else {
                        right.refine_with(path_condition, depth + 1)
                    }
                } else if path_condition.implies_not(right) {
                    left.refine_with(path_condition, depth + 1)
                } else {
                    left.refine_with(path_condition, depth + 1)
                        .or(right.refine_with(path_condition, depth + 1))
                }
            }
            Expression::Reference(..) | Expression::InitialParameterValue { .. } => {
                // We could refine their paths, which will increase precision, but it does not
                // currently seem cost-effective. This does not affect soundness.
                self.clone()
            }
            Expression::Rem { left, right } => left
                .refine_with(path_condition, depth + 1)
                .remainder(right.refine_with(path_condition, depth + 1)),
            Expression::Shl { left, right } => left
                .refine_with(path_condition, depth + 1)
                .shift_left(right.refine_with(path_condition, depth + 1)),
            Expression::ShlOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_with(path_condition, depth + 1)
                .shl_overflows(right.refine_with(path_condition, depth + 1), *result_type),
            Expression::Shr { left, right } => left
                .refine_with(path_condition, depth + 1)
                .shr(right.refine_with(path_condition, depth + 1)),
            Expression::ShrOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_with(path_condition, depth + 1)
                .shr_overflows(right.refine_with(path_condition, depth + 1), *result_type),
            Expression::Sub { left, right } => left
                .refine_with(path_condition, depth + 1)
                .subtract(right.refine_with(path_condition, depth + 1)),
            Expression::SubOverflows {
                left,
                right,
                result_type,
            } => left
                .refine_with(path_condition, depth + 1)
                .sub_overflows(right.refine_with(path_condition, depth + 1), *result_type),
            Expression::Switch {
                discriminator,
                cases,
                default,
            } => discriminator.refine_with(path_condition, depth + 1).switch(
                cases
                    .iter()
                    .map(|(case_val, result_val)| {
                        (
                            case_val.refine_with(path_condition, depth + 1),
                            result_val.refine_with(path_condition, depth + 1),
                        )
                    })
                    .collect(),
                default.refine_with(path_condition, depth + 1),
            ),
            Expression::TaggedExpression { operand, tag } => {
                operand.refine_with(path_condition, depth + 1).add_tag(*tag)
            }
            Expression::Transmute {
                operand,
                target_type,
            } => operand
                .refine_with(path_condition, depth + 1)
                .transmute(*target_type),
            Expression::UninterpretedCall {
                callee,
                arguments,
                result_type,
                path,
            } => callee
                .refine_with(path_condition, depth + 1)
                .uninterpreted_call(
                    arguments
                        .iter()
                        .map(|v| v.refine_with(path_condition, depth + 1))
                        .collect(),
                    *result_type,
                    path.clone(),
                ),
            Expression::UnknownModelField { .. } => self.clone(),
            Expression::UnknownTagCheck {
                operand,
                tag,
                checking_presence,
            } => AbstractValue::make_tag_check(
                operand.refine_with(path_condition, depth + 1),
                *tag,
                *checking_presence,
            ),
            Expression::UnknownTagField { .. } => self.clone(),
            Expression::Variable { var_type, .. } => {
                if *var_type == ExpressionType::Bool {
                    if path_condition.implies(self) {
                        return Rc::new(TRUE);
                    } else if path_condition.implies_not(self) {
                        return Rc::new(FALSE);
                    }
                }
                self.clone()
            }
            Expression::WidenedJoin { path, operand } => {
                operand.refine_with(path_condition, depth + 1).widen(path)
            }
        }
    }

    /// Given a left-hand expression that occurs in a Path that is in a root position, look for an embedded
    /// path that is rooted in old_root and replace the path with one that is rooted in new_root.
    #[logfn_inputs(TRACE)]
    fn replace_embedded_path_root(
        &self,
        old_root: &Rc<Path>,
        new_root: Rc<Path>,
    ) -> Rc<AbstractValue> {
        match &self.expression {
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => {
                let replaced_consequent =
                    consequent.replace_embedded_path_root(old_root, new_root.clone());
                let replaced_alternate = alternate.replace_embedded_path_root(old_root, new_root);
                condition.conditional_expression(replaced_consequent, replaced_alternate)
            }
            Expression::InitialParameterValue { path, var_type } => {
                AbstractValue::make_initial_parameter_value(
                    *var_type,
                    path.replace_root(old_root, new_root),
                )
            }
            Expression::Join { left, right } => left
                .replace_embedded_path_root(old_root, new_root.clone())
                .join(right.replace_embedded_path_root(old_root, new_root)),
            Expression::Offset { left, right } => left
                .replace_embedded_path_root(old_root, new_root)
                .offset(right.clone()),
            Expression::Reference(path) => {
                AbstractValue::make_reference(path.replace_root(old_root, new_root))
            }
            Expression::Variable { path, var_type } => {
                AbstractValue::make_typed_unknown(*var_type, path.replace_root(old_root, new_root))
            }
            Expression::WidenedJoin { path, operand } => {
                operand.widen(&path.replace_root(old_root, new_root))
            }
            _ => {
                if self.is_top() || self.is_bottom() {
                    return self.clone();
                }
                info!(
                    "replacing embedded path root of {:?}, old_root {:?}, new_root {:?}",
                    self, old_root, new_root
                );
                self.clone()
            }
        }
    }

    /// A cast that re-interprets existing bits rather than doing conversions.
    /// When the source type and target types differ in length, bits are truncated
    /// or zero filled as appropriate.
    #[logfn(TRACE)]
    fn transmute(&self, target_type: ExpressionType) -> Rc<AbstractValue> {
        if target_type.is_integer() && self.expression.infer_type().is_integer() {
            self.unsigned_modulo(target_type.bit_length())
                .cast(target_type)
        } else if target_type == ExpressionType::Bool {
            self.unsigned_modulo(target_type.bit_length())
                .not_equals(Rc::new(ConstantDomain::U128(0).into()))
        } else {
            self.try_to_constant_fold_and_distribute_typed_unary_op(
                target_type,
                ConstantDomain::transmute,
                Self::transmute,
                |o, t| {
                    AbstractValue::make_typed_unary(o, t, |operand, target_type| {
                        Expression::Transmute {
                            operand,
                            target_type,
                        }
                    })
                },
            )
        }
    }

    #[logfn_inputs(TRACE)]
    #[logfn(TRACE)]
    fn try_resolve_as_byte_array(&self, environment: &Environment) -> Option<Vec<u8>> {
        if let Expression::Reference(path) = &self.expression {
            if matches!(&path.value, PathEnum::HeapBlock { .. }) {
                let heap_layout_path = Path::new_layout(path.clone());
                if let Some(layout) = environment.value_at(&heap_layout_path) {
                    if let Expression::HeapBlockLayout { length, .. } = &layout.expression {
                        if let Expression::CompileTimeConstant(ConstantDomain::U128(len)) =
                            length.expression
                        {
                            let mut arr = Vec::with_capacity(len as usize);
                            for i in 0..(len as usize) {
                                let elem_index = Rc::new(ConstantDomain::U128(i as u128).into());
                                let elem_path = Path::new_index(path.clone(), elem_index);
                                let elem_val = environment.value_at(&elem_path);
                                if let Some(val) = elem_val {
                                    if let Expression::CompileTimeConstant(ConstantDomain::U128(
                                        v,
                                    )) = &val.expression
                                    {
                                        arr.push(*v as u8);
                                        continue;
                                    }
                                }
                                return None;
                            }
                            return Some(arr);
                        }
                    }
                }
            }
        }
        None
    }

    #[logfn_inputs(TRACE)]
    #[logfn(TRACE)]
    fn try_resolve_as_ref_to_str(&self, _environment: &Environment) -> Option<Rc<str>> {
        if let Expression::Variable {
            path,
            var_type: ExpressionType::ThinPointer,
        } = &self.expression
        {
            if let PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } = &path.value
            {
                if let (PathEnum::Computed { value }, PathSelector::Field(0)) =
                    (&qualifier.value, selector.as_ref())
                {
                    if let Expression::CompileTimeConstant(ConstantDomain::Str(s)) =
                        &value.expression
                    {
                        return Some(s.clone());
                    }
                }
            }
        }
        None
    }

    /// Returns a domain whose corresponding set of concrete values include all of the values
    /// that the call expression might return at runtime. The function to be called will not
    /// have been summarized for some reason or another (for example, it might be a foreign function).
    #[logfn_inputs(TRACE)]
    fn uninterpreted_call(
        &self,
        arguments: Vec<Rc<AbstractValue>>,
        result_type: ExpressionType,
        path: Rc<Path>,
    ) -> Rc<AbstractValue> {
        AbstractValue::make_uninterpreted_call(self.clone(), arguments, result_type, path)
    }

    /// Returns an expression that discards (zero fills) bits that are not in the specified number
    /// of least significant bits. The result is an unsigned integer.
    #[logfn(TRACE)]
    fn unsigned_modulo(&self, num_bits: u8) -> Rc<AbstractValue> {
        if let Expression::CompileTimeConstant(c) = &self.expression {
            Rc::new(c.unsigned_modulo(num_bits).into())
        } else if num_bits == 128 {
            self.try_to_retype_as(ExpressionType::U128)
        } else {
            let power_of_two = Rc::new(ConstantDomain::U128(1 << num_bits).into());
            let unsigned = self.try_to_retype_as(ExpressionType::U128);
            unsigned.remainder(power_of_two)
        }
    }

    /// Returns an expression that shifts the bit representation of the value to the left by the
    /// given number of bits, filling in with zeroes. The result is an unsigned integer.
    #[logfn(TRACE)]
    fn unsigned_shift_left(&self, num_bits: u8) -> Rc<AbstractValue> {
        if let Expression::CompileTimeConstant(c) = &self.expression {
            Rc::new(c.unsigned_shift_left(num_bits).into())
        } else {
            let power_of_two = Rc::new(ConstantDomain::U128(1 << num_bits).into());
            let unsigned = self.try_to_retype_as(ExpressionType::U128);
            unsigned.multiply(power_of_two)
        }
    }

    /// Returns an expression that shifts the bit representation of the value to the right by the
    /// given number of bits, filling in with zeroes. The result is an unsigned integer.
    #[logfn(TRACE)]
    fn unsigned_shift_right(&self, num_bits: u8) -> Rc<AbstractValue> {
        if let Expression::CompileTimeConstant(c) = &self.expression {
            Rc::new(c.unsigned_shift_right(num_bits).into())
        } else {
            let power_of_two = Rc::new(ConstantDomain::U128(1 << num_bits).into());
            let unsigned = self.try_to_retype_as(ExpressionType::U128);
            unsigned.divide(power_of_two)
        }
    }

    /// Returns true if the expression uses any of the variables in the given set.
    #[logfn(TRACE)]
    fn uses(&self, variables: &HashSet<Rc<Path>>) -> bool {
        match &self.expression {
            Expression::Bottom => false,
            Expression::Top => true,
            Expression::Add { left, right }
            | Expression::AddOverflows { left, right, .. }
            | Expression::And { left, right }
            | Expression::BitAnd { left, right }
            | Expression::BitOr { left, right }
            | Expression::BitXor { left, right }
            | Expression::Div { left, right }
            | Expression::Equals { left, right }
            | Expression::GreaterOrEqual { left, right }
            | Expression::GreaterThan { left, right }
            | Expression::IntrinsicBinary { left, right, .. }
            | Expression::LessOrEqual { left, right }
            | Expression::LessThan { left, right }
            | Expression::Mul { left, right }
            | Expression::MulOverflows { left, right, .. }
            | Expression::Ne { left, right }
            | Expression::Offset { left, right }
            | Expression::Or { left, right }
            | Expression::Rem { left, right }
            | Expression::Shl { left, right }
            | Expression::ShlOverflows { left, right, .. }
            | Expression::Shr { left, right, .. }
            | Expression::ShrOverflows { left, right, .. }
            | Expression::Sub { left, right }
            | Expression::SubOverflows { left, right, .. } => {
                left.uses(variables) || right.uses(variables)
            }
            Expression::BitNot { operand, .. }
            | Expression::Cast { operand, .. }
            | Expression::IntrinsicBitVectorUnary { operand, .. }
            | Expression::IntrinsicFloatingPointUnary { operand, .. }
            | Expression::Neg { operand }
            | Expression::LogicalNot { operand }
            | Expression::TaggedExpression { operand, .. }
            | Expression::Transmute { operand, .. }
            | Expression::UnknownTagCheck { operand, .. } => operand.uses(variables),
            Expression::CompileTimeConstant(..) => false,
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => {
                condition.uses(variables) || consequent.uses(variables) || alternate.uses(variables)
            }
            Expression::HeapBlock { .. } => false,
            Expression::HeapBlockLayout {
                length, alignment, ..
            } => length.uses(variables) || alignment.uses(variables),
            Expression::Join { left, right } => left.uses(variables) || right.uses(variables),
            Expression::Memcmp {
                left,
                right,
                length,
            } => left.uses(variables) || right.uses(variables) || length.uses(variables),
            Expression::Reference(path)
            | Expression::InitialParameterValue { path, .. }
            | Expression::UnknownTagField { path }
            | Expression::Variable { path, .. } => variables.contains(path),
            Expression::Switch {
                discriminator,
                cases,
                default,
            } => {
                discriminator.uses(variables)
                    || default.uses(variables)
                    || cases.iter().any(|(case_val, result_val)| {
                        case_val.uses(variables) || result_val.uses(variables)
                    })
            }
            Expression::UninterpretedCall {
                callee,
                arguments: args,
                ..
            } => callee.uses(variables) || args.iter().any(|arg| arg.uses(variables)),
            Expression::UnknownModelField { path, default } => {
                variables.contains(path) || default.uses(variables)
            }
            Expression::WidenedJoin { operand, path } => {
                operand.uses(variables) || variables.contains(path)
            }
        }
    }

    /// Returns an abstract value whose corresponding set of concrete values include all of the values
    /// corresponding to self and other. The set of values may be less precise (more inclusive) than
    /// the set returned by join. The chief requirement is that a small number of widen calls
    /// deterministically lead to a set of values that include of the values that could be stored
    /// in memory at the given path.
    #[logfn_inputs(TRACE)]
    fn widen(&self, path: &Rc<Path>) -> Rc<AbstractValue> {
        match &self.expression {
            Expression::Join { .. } => AbstractValue::make_from(
                Expression::WidenedJoin {
                    path: path.clone(),
                    operand: self.clone(),
                },
                self.expression_size.saturating_add(1),
            ),
            _ => self.clone(),
        }
    }
}
