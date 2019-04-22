// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
#![allow(clippy::float_cmp)]

use crate::expression::{Expression, ExpressionType};
use crate::summaries::PersistentSummaryCache;
use crate::utils::is_rust_intrinsic;

use rustc::hir::def_id::DefId;
use rustc::ty::TyCtxt;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Abstracts over constant values referenced in MIR and adds information
/// that is useful for the abstract interpreter. More importantly, this
/// value can be serialized to the persistent summary cache.

#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialOrd, PartialEq, Hash, Ord)]
pub enum ConstantDomain {
    /// The impossible constant. Use this as the result of a partial transfer function.
    Bottom,
    /// The primitive character type; holds a Unicode scalar value (a non-surrogate code point).
    Char(char),
    /// The Boolean value false.
    False,
    /// A reference to a function.
    Function {
        /// The crate specific key that is used to identify the function in the current crate.
        /// This is not available for functions returned by calls to functions from other crates,
        /// since the def id the other crates use have no meaning for the current crate.
        #[serde(skip)]
        def_id: Option<DefId>,
        /// Indicates if the function is known to be treated specially by the Rust compiler
        is_intrinsic: bool,
        /// The key to use when retrieving a summary for the function from the summary cache
        summary_cache_key: String,
    },
    /// Signed 16 byte integer.
    I128(i128),
    /// 64 bit floating point, stored as a u64 to make it comparable.
    F64(u64),
    /// 32 bit floating point, stored as a u32 to make it comparable.
    F32(u32),
    /// A string literal.
    Str(String),
    /// The Boolean true value.
    True,
    /// Unsigned 16 byte integer.
    U128(u128),
    /// A place holder for other kinds of constants. Eventually this goes away.
    Unimplemented,
}

/// Constructors
impl ConstantDomain {
    /// Returns a constant value that is a reference to a function
    pub fn for_function(
        def_id: DefId,
        tcx: &TyCtxt<'_, '_, '_>,
        summary_cache: &mut PersistentSummaryCache<'_, '_>,
    ) -> ConstantDomain {
        let summary_cache_key = summary_cache.get_summary_key_for(def_id);
        ConstantDomain::Function {
            def_id: Some(def_id),
            is_intrinsic: is_rust_intrinsic(def_id, tcx),
            summary_cache_key: summary_cache_key.to_owned(),
        }
    }
}

impl From<bool> for ConstantDomain {
    fn from(b: bool) -> ConstantDomain {
        if b {
            ConstantDomain::True
        } else {
            ConstantDomain::False
        }
    }
}

/// Transfer functions
impl ConstantDomain {
    /// Returns a constant that is "self + other".
    pub fn add(&self, other: &Self) -> Self {
        match (self, other) {
            (ConstantDomain::F32(val1), ConstantDomain::F32(val2)) => {
                ConstantDomain::F32((f32::from_bits(*val1) + f32::from_bits(*val2)).to_bits())
            }
            (ConstantDomain::F64(val1), ConstantDomain::F64(val2)) => {
                ConstantDomain::F64((f64::from_bits(*val1) + f64::from_bits(*val2)).to_bits())
            }
            (ConstantDomain::I128(val1), ConstantDomain::I128(val2)) => {
                ConstantDomain::I128(val1.wrapping_add(*val2))
            }
            (ConstantDomain::U128(val1), ConstantDomain::U128(val2)) => {
                ConstantDomain::U128(val1.wrapping_add(*val2))
            }
            _ => ConstantDomain::Bottom,
        }
    }

    /// Returns a constant that is true if "self + other" is not in range of target_type.
    pub fn add_overflows(&self, other: &Self, target_type: &ExpressionType) -> Self {
        match (&self, &other) {
            (ConstantDomain::I128(val1), ConstantDomain::I128(val2)) => match target_type {
                ExpressionType::Isize => isize::overflowing_add(*val1 as isize, *val2 as isize).1,
                ExpressionType::I128 => i128::overflowing_add(*val1, *val2).1,
                ExpressionType::I64 => i64::overflowing_add(*val1 as i64, *val2 as i64).1,
                ExpressionType::I32 => i32::overflowing_add(*val1 as i32, *val2 as i32).1,
                ExpressionType::I16 => i16::overflowing_add(*val1 as i16, *val2 as i16).1,
                ExpressionType::I8 => i8::overflowing_add(*val1 as i8, *val2 as i8).1,
                _ => unreachable!("{:?}", target_type),
            }
            .into(),
            (ConstantDomain::U128(val1), ConstantDomain::U128(val2)) => match target_type {
                ExpressionType::Usize => usize::overflowing_add(*val1 as usize, *val2 as usize).1,
                ExpressionType::U128 => u128::overflowing_add(*val1, *val2).1,
                ExpressionType::U64 => u64::overflowing_add(*val1 as u64, *val2 as u64).1,
                ExpressionType::U32 => u32::overflowing_add(*val1 as u32, *val2 as u32).1,
                ExpressionType::U16 => u16::overflowing_add(*val1 as u16, *val2 as u16).1,
                ExpressionType::U8 => u8::overflowing_add(*val1 as u8, *val2 as u8).1,
                _ => unreachable!("{:?}", target_type),
            }
            .into(),
            _ => ConstantDomain::Bottom,
        }
    }

    /// Returns a constant that is "self & other".
    pub fn bit_and(&self, other: &Self) -> Self {
        match (&self, &other) {
            (ConstantDomain::I128(val1), ConstantDomain::I128(val2)) => {
                ConstantDomain::I128(val1 & val2)
            }
            (ConstantDomain::U128(val1), ConstantDomain::U128(val2)) => {
                ConstantDomain::U128(val1 & val2)
            }
            (ConstantDomain::True, ConstantDomain::True) => ConstantDomain::True,
            (ConstantDomain::False, _) | (_, ConstantDomain::False) => ConstantDomain::False,
            _ => ConstantDomain::Bottom,
        }
    }

    /// Returns a constant that is "self | other".
    pub fn bit_or(&self, other: &Self) -> Self {
        match (&self, &other) {
            (ConstantDomain::I128(val1), ConstantDomain::I128(val2)) => {
                ConstantDomain::I128(val1 | val2)
            }
            (ConstantDomain::U128(val1), ConstantDomain::U128(val2)) => {
                ConstantDomain::U128(val1 | val2)
            }
            (ConstantDomain::False, ConstantDomain::False) => ConstantDomain::False,
            (ConstantDomain::True, _) | (_, ConstantDomain::True) => ConstantDomain::True,
            _ => ConstantDomain::Bottom,
        }
    }

    /// Returns a constant that is "self ^ other".
    pub fn bit_xor(&self, other: &Self) -> Self {
        match (&self, &other) {
            (ConstantDomain::I128(val1), ConstantDomain::I128(val2)) => {
                ConstantDomain::I128(val1 ^ val2)
            }
            (ConstantDomain::U128(val1), ConstantDomain::U128(val2)) => {
                ConstantDomain::U128(val1 ^ val2)
            }
            (ConstantDomain::False, ConstantDomain::False)
            | (ConstantDomain::True, ConstantDomain::True) => ConstantDomain::False,
            (ConstantDomain::True, ConstantDomain::False)
            | (ConstantDomain::False, ConstantDomain::True) => ConstantDomain::True,
            _ => ConstantDomain::Bottom,
        }
    }

    /// Returns a constant that is "self as target_type"
    #[allow(clippy::cast_lossless)]
    pub fn cast(&self, target_type: &ExpressionType) -> Self {
        match self {
            ConstantDomain::Bottom => self.clone(),
            ConstantDomain::Char(ch) => {
                let char_as_int_const = ConstantDomain::U128(u128::from(*ch as u32));
                char_as_int_const.cast(target_type)
            }
            ConstantDomain::False => {
                if target_type.is_signed_integer() {
                    ConstantDomain::I128(0)
                } else {
                    ConstantDomain::U128(0)
                }
            }
            ConstantDomain::True => {
                if target_type.is_signed_integer() {
                    ConstantDomain::I128(1)
                } else {
                    ConstantDomain::U128(1)
                }
            }
            ConstantDomain::U128(val) => {
                if *target_type == ExpressionType::Char {
                    ConstantDomain::Char((*val as u8) as char)
                } else if target_type.is_signed_integer() {
                    ConstantDomain::I128(*val as i128).cast(target_type)
                } else {
                    match target_type {
                        ExpressionType::U8 => ConstantDomain::U128((*val as u8) as u128),
                        ExpressionType::U16 => ConstantDomain::U128((*val as u16) as u128),
                        ExpressionType::U32 => ConstantDomain::U128((*val as u32) as u128),
                        ExpressionType::U64 => ConstantDomain::U128((*val as u64) as u128),
                        _ => self.clone(),
                    }
                }
            }
            ConstantDomain::I128(val) => {
                if target_type.is_unsigned_integer() {
                    ConstantDomain::U128(*val as u128).cast(target_type)
                } else {
                    match target_type {
                        ExpressionType::I8 => ConstantDomain::I128((*val as i8) as i128),
                        ExpressionType::I16 => ConstantDomain::I128((*val as i16) as i128),
                        ExpressionType::I32 => ConstantDomain::I128((*val as i32) as i128),
                        ExpressionType::I64 => ConstantDomain::I128((*val as i64) as i128),
                        _ => self.clone(),
                    }
                }
            }
            ConstantDomain::F32(val) => {
                let f = f32::from_bits(*val);
                if *target_type == ExpressionType::F64 {
                    ConstantDomain::F64((f as f64).to_bits())
                } else if target_type.is_signed_integer() {
                    ConstantDomain::I128(f as i128).cast(target_type)
                } else if target_type.is_unsigned_integer() {
                    ConstantDomain::U128(f as u128).cast(target_type)
                } else {
                    self.clone()
                }
            }
            ConstantDomain::F64(val) => {
                let f = f64::from_bits(*val);
                if *target_type == ExpressionType::F32 {
                    ConstantDomain::F32((f as f32).to_bits())
                } else if target_type.is_signed_integer() {
                    ConstantDomain::I128(f as i128).cast(target_type)
                } else if target_type.is_unsigned_integer() {
                    ConstantDomain::U128(f as u128).cast(target_type)
                } else {
                    self.clone()
                }
            }
            _ => self.clone(),
        }
    }

    /// Returns a constant that is "self / other".
    pub fn div(&self, other: &Self) -> Self {
        match (&self, &other) {
            (ConstantDomain::F32(val1), ConstantDomain::F32(val2)) => {
                let result = f32::from_bits(*val1) / f32::from_bits(*val2);
                ConstantDomain::F32(result.to_bits())
            }
            (ConstantDomain::F64(val1), ConstantDomain::F64(val2)) => {
                let result = f64::from_bits(*val1) / f64::from_bits(*val2);
                ConstantDomain::F64(result.to_bits())
            }
            (ConstantDomain::I128(val1), ConstantDomain::I128(val2)) => {
                if *val2 == 0 {
                    ConstantDomain::Bottom
                } else {
                    val1.checked_div(*val2)
                        .map(ConstantDomain::I128)
                        .unwrap_or(ConstantDomain::Bottom)
                }
            }
            (ConstantDomain::U128(val1), ConstantDomain::U128(val2)) => {
                if *val2 == 0 {
                    ConstantDomain::Bottom
                } else {
                    ConstantDomain::U128(*val1 / *val2)
                }
            }
            _ => ConstantDomain::Bottom,
        }
    }

    /// Returns a constant that is "self == other".
    pub fn equals(&self, other: &Self) -> Self {
        match (&self, &other) {
            (ConstantDomain::F32(val1), ConstantDomain::F32(val2)) => {
                f32::from_bits(*val1) == f32::from_bits(*val2)
            }
            (ConstantDomain::F64(val1), ConstantDomain::F64(val2)) => {
                f64::from_bits(*val1) == f64::from_bits(*val2)
            }
            _ => *self == *other,
        }
        .into()
    }

    /// Returns a constant that is "self >= other".
    pub fn greater_or_equal(&self, other: &Self) -> Self {
        match (&self, &other) {
            (ConstantDomain::F32(val1), ConstantDomain::F32(val2)) => {
                f32::from_bits(*val1) >= f32::from_bits(*val2)
            }
            (ConstantDomain::F64(val1), ConstantDomain::F64(val2)) => {
                f64::from_bits(*val1) >= f64::from_bits(*val2)
            }
            _ => *self >= *other,
        }
        .into()
    }

    /// Returns a constant that is "self > other".
    pub fn greater_than(&self, other: &Self) -> Self {
        match (&self, &other) {
            (ConstantDomain::F32(val1), ConstantDomain::F32(val2)) => {
                f32::from_bits(*val1) > f32::from_bits(*val2)
            }
            (ConstantDomain::F64(val1), ConstantDomain::F64(val2)) => {
                f64::from_bits(*val1) > f64::from_bits(*val2)
            }
            _ => *self > *other,
        }
        .into()
    }

    /// Returns a constant that is "self <= other".
    pub fn less_or_equal(&self, other: &Self) -> Self {
        match (&self, &other) {
            (ConstantDomain::F32(val1), ConstantDomain::F32(val2)) => {
                f32::from_bits(*val1) <= f32::from_bits(*val2)
            }
            (ConstantDomain::F64(val1), ConstantDomain::F64(val2)) => {
                f64::from_bits(*val1) <= f64::from_bits(*val2)
            }
            _ => *self <= *other,
        }
        .into()
    }

    /// Returns a constant that is "self < other".
    pub fn less_than(&self, other: &Self) -> Self {
        match (&self, &other) {
            (ConstantDomain::F32(val1), ConstantDomain::F32(val2)) => {
                f32::from_bits(*val1) < f32::from_bits(*val2)
            }
            (ConstantDomain::F64(val1), ConstantDomain::F64(val2)) => {
                f64::from_bits(*val1) < f64::from_bits(*val2)
            }
            _ => *self < *other,
        }
        .into()
    }

    /// Returns a constant that is "self * other".
    pub fn mul(&self, other: &Self) -> Self {
        match (&self, &other) {
            (ConstantDomain::F32(val1), ConstantDomain::F32(val2)) => {
                let result = f32::from_bits(*val1) * f32::from_bits(*val2);
                ConstantDomain::F32(result.to_bits())
            }
            (ConstantDomain::F64(val1), ConstantDomain::F64(val2)) => {
                let result = f64::from_bits(*val1) * f64::from_bits(*val2);
                ConstantDomain::F64(result.to_bits())
            }
            (ConstantDomain::I128(val1), ConstantDomain::I128(val2)) => {
                ConstantDomain::I128(val1.wrapping_mul(*val2))
            }
            (ConstantDomain::U128(val1), ConstantDomain::U128(val2)) => {
                ConstantDomain::U128(val1.wrapping_mul(*val2))
            }
            _ => ConstantDomain::Bottom,
        }
    }

    /// Returns a constant that is true if "self * other" is not in range of target_type.
    pub fn mul_overflows(&self, other: &Self, target_type: &ExpressionType) -> Self {
        match (&self, &other) {
            (ConstantDomain::I128(val1), ConstantDomain::I128(val2)) => {
                let result = match target_type {
                    ExpressionType::Isize => {
                        isize::overflowing_mul(*val1 as isize, *val2 as isize).1
                    }
                    ExpressionType::I128 => i128::overflowing_mul(*val1, *val2).1,
                    ExpressionType::I64 => i64::overflowing_mul(*val1 as i64, *val2 as i64).1,
                    ExpressionType::I32 => i32::overflowing_mul(*val1 as i32, *val2 as i32).1,
                    ExpressionType::I16 => i16::overflowing_mul(*val1 as i16, *val2 as i16).1,
                    ExpressionType::I8 => i8::overflowing_mul(*val1 as i8, *val2 as i8).1,
                    _ => unreachable!("target_type {:?}", target_type),
                };
                result.into()
            }
            (ConstantDomain::U128(val1), ConstantDomain::U128(val2)) => {
                let result = match target_type {
                    ExpressionType::Usize => {
                        usize::overflowing_mul(*val1 as usize, *val2 as usize).1
                    }
                    ExpressionType::U128 => u128::overflowing_mul(*val1, *val2).1,
                    ExpressionType::U64 => u64::overflowing_mul(*val1 as u64, *val2 as u64).1,
                    ExpressionType::U32 => u32::overflowing_mul(*val1 as u32, *val2 as u32).1,
                    ExpressionType::U16 => u16::overflowing_mul(*val1 as u16, *val2 as u16).1,
                    ExpressionType::U8 => u8::overflowing_mul(*val1 as u8, *val2 as u8).1,
                    _ => unreachable!("target_type {:?}", target_type),
                };
                result.into()
            }
            _ => ConstantDomain::Bottom,
        }
    }

    /// Returns a constant that is "-self".
    pub fn neg(&self) -> Self {
        match self {
            ConstantDomain::F32(val) => {
                let result = -f32::from_bits(*val);
                ConstantDomain::F32(result.to_bits())
            }
            ConstantDomain::F64(val) => {
                let result = -f64::from_bits(*val);
                ConstantDomain::F64(result.to_bits())
            }
            ConstantDomain::I128(val) => ConstantDomain::I128(val.wrapping_neg()),
            ConstantDomain::U128(val) => ConstantDomain::U128(val.wrapping_neg()),
            _ => ConstantDomain::Bottom,
        }
    }

    /// Returns a constant that is "self != other".
    pub fn not_equals(&self, other: &Self) -> Self {
        match (&self, &other) {
            (ConstantDomain::F32(val1), ConstantDomain::F32(val2)) => {
                f32::from_bits(*val1) != f32::from_bits(*val2)
            }
            (ConstantDomain::F64(val1), ConstantDomain::F64(val2)) => {
                f64::from_bits(*val1) != f64::from_bits(*val2)
            }
            _ => *self != *other,
        }
        .into()
    }

    /// Returns a constant that is "!self".
    pub fn not(&self) -> Self {
        match &self {
            ConstantDomain::False => ConstantDomain::True,
            ConstantDomain::True => ConstantDomain::False,
            _ => ConstantDomain::Bottom,
        }
    }

    /// Returns a constant that is "self % other".
    pub fn rem(&self, other: &Self) -> Self {
        match (&self, &other) {
            (ConstantDomain::F32(val1), ConstantDomain::F32(val2)) => {
                let result = f32::from_bits(*val1) % f32::from_bits(*val2);
                ConstantDomain::F32(result.to_bits())
            }
            (ConstantDomain::F64(val1), ConstantDomain::F64(val2)) => {
                let result = f64::from_bits(*val1) % f64::from_bits(*val2);
                ConstantDomain::F64(result.to_bits())
            }
            (ConstantDomain::I128(val1), ConstantDomain::I128(val2)) => {
                if *val2 == 0 {
                    ConstantDomain::Bottom
                } else {
                    ConstantDomain::I128(val1.wrapping_rem(*val2))
                }
            }
            (ConstantDomain::U128(val1), ConstantDomain::U128(val2)) => {
                if *val2 == 0 {
                    ConstantDomain::Bottom
                } else {
                    ConstantDomain::U128(val1.wrapping_rem(*val2))
                }
            }
            _ => ConstantDomain::Bottom,
        }
    }

    /// Returns a constant that is "self << other".
    pub fn shl(&self, other: &Self) -> Self {
        let other_as_u32 = match &other {
            ConstantDomain::I128(val2) => Some(*val2 as u32),
            ConstantDomain::U128(val2) => Some(*val2 as u32),
            _ => None,
        };
        match (&self, other_as_u32) {
            (ConstantDomain::I128(val1), Some(val2)) => {
                ConstantDomain::I128(val1.wrapping_shl(val2))
            }
            (ConstantDomain::U128(val1), Some(val2)) => {
                ConstantDomain::U128(val1.wrapping_shl(val2))
            }
            _ => ConstantDomain::Bottom,
        }
    }

    /// Returns a constant that is true if "self << other" is not in range of target_type.
    pub fn shl_overflows(&self, other: &Self, target_type: &ExpressionType) -> Self {
        let other_as_u32 = match &other {
            ConstantDomain::I128(val2) => Some(*val2 as u32),
            ConstantDomain::U128(val2) => Some(*val2 as u32),
            _ => None,
        };
        match (&self, other_as_u32) {
            (ConstantDomain::I128(val1), Some(val2)) => match target_type {
                ExpressionType::Isize => isize::overflowing_shl(*val1 as isize, val2).1,
                ExpressionType::I128 => i128::overflowing_shl(*val1, val2).1,
                ExpressionType::I64 => i64::overflowing_shl(*val1 as i64, val2).1,
                ExpressionType::I32 => i32::overflowing_shl(*val1 as i32, val2).1,
                ExpressionType::I16 => i16::overflowing_shl(*val1 as i16, val2).1,
                ExpressionType::I8 => i8::overflowing_shl(*val1 as i8, val2).1,
                _ => unreachable!("{:?}", target_type),
            }
            .into(),
            (ConstantDomain::U128(val1), Some(val2)) => match target_type {
                ExpressionType::Usize => usize::overflowing_shl(*val1 as usize, val2).1,
                ExpressionType::U128 => u128::overflowing_shl(*val1, val2).1,
                ExpressionType::U64 => u64::overflowing_shl(*val1 as u64, val2).1,
                ExpressionType::U32 => u32::overflowing_shl(*val1 as u32, val2).1,
                ExpressionType::U16 => u16::overflowing_shl(*val1 as u16, val2).1,
                ExpressionType::U8 => u8::overflowing_shl(*val1 as u8, val2).1,
                _ => unreachable!("{:?}", target_type),
            }
            .into(),
            _ => ConstantDomain::Bottom,
        }
    }

    /// Returns a constant that is "self >> other".
    pub fn shr(&self, other: &Self) -> Self {
        let other_as_u32 = match &other {
            ConstantDomain::I128(val2) => Some(*val2 as u32),
            ConstantDomain::U128(val2) => Some(*val2 as u32),
            _ => None,
        };
        match (&self, other_as_u32) {
            (ConstantDomain::I128(val1), Some(val2)) => {
                ConstantDomain::I128(val1.wrapping_shr(val2))
            }
            (ConstantDomain::U128(val1), Some(val2)) => {
                ConstantDomain::U128(val1.wrapping_shr(val2))
            }
            _ => ConstantDomain::Bottom,
        }
    }

    /// Returns a constant that is true if "self >> other" shifts away all bits.
    pub fn shr_overflows(&self, other: &Self, target_type: &ExpressionType) -> Self {
        let other_as_u32 = match &other {
            ConstantDomain::I128(val2) => Some(*val2 as u32),
            ConstantDomain::U128(val2) => Some(*val2 as u32),
            _ => None,
        };
        match (&self, other_as_u32) {
            (ConstantDomain::I128(val1), Some(val2)) => match target_type {
                ExpressionType::Isize => isize::overflowing_shl(*val1 as isize, val2).1,
                ExpressionType::I128 => i128::overflowing_shl(*val1, val2).1,
                ExpressionType::I64 => i64::overflowing_shl(*val1 as i64, val2).1,
                ExpressionType::I32 => i32::overflowing_shl(*val1 as i32, val2).1,
                ExpressionType::I16 => i16::overflowing_shl(*val1 as i16, val2).1,
                ExpressionType::I8 => i8::overflowing_shl(*val1 as i8, val2).1,
                _ => unreachable!("{:?}", target_type),
            }
            .into(),
            (ConstantDomain::U128(val1), Some(val2)) => match target_type {
                ExpressionType::Usize => usize::overflowing_shl(*val1 as usize, val2).1,
                ExpressionType::U128 => u128::overflowing_shl(*val1, val2).1,
                ExpressionType::U64 => u64::overflowing_shl(*val1 as u64, val2).1,
                ExpressionType::U32 => u32::overflowing_shl(*val1 as u32, val2).1,
                ExpressionType::U16 => u16::overflowing_shl(*val1 as u16, val2).1,
                ExpressionType::U8 => u8::overflowing_shl(*val1 as u8, val2).1,
                _ => unreachable!("{:?}", target_type),
            }
            .into(),
            _ => ConstantDomain::Bottom,
        }
    }

    /// Returns a constant that is "self - other".
    pub fn sub(&self, other: &Self) -> Self {
        match (self, other) {
            (ConstantDomain::F32(val1), ConstantDomain::F32(val2)) => {
                let result = f32::from_bits(*val1) - f32::from_bits(*val2);
                ConstantDomain::F32(result.to_bits())
            }
            (ConstantDomain::F64(val1), ConstantDomain::F64(val2)) => {
                let result = f64::from_bits(*val1) - f64::from_bits(*val2);
                ConstantDomain::F64(result.to_bits())
            }
            (ConstantDomain::I128(val1), ConstantDomain::I128(val2)) => {
                ConstantDomain::I128(val1.wrapping_sub(*val2))
            }
            (ConstantDomain::U128(val1), ConstantDomain::U128(val2)) => {
                ConstantDomain::U128(val1.wrapping_sub(*val2))
            }
            _ => ConstantDomain::Bottom,
        }
    }

    /// Returns a constant that is true if "self - other" is not in range of target_type.
    pub fn sub_overflows(&self, other: &Self, target_type: &ExpressionType) -> Self {
        match (&self, &other) {
            (ConstantDomain::I128(val1), ConstantDomain::I128(val2)) => match target_type {
                ExpressionType::Isize => isize::overflowing_add(*val1 as isize, *val2 as isize).1,
                ExpressionType::I128 => i128::overflowing_add(*val1, *val2).1,
                ExpressionType::I64 => i64::overflowing_add(*val1 as i64, *val2 as i64).1,
                ExpressionType::I32 => i32::overflowing_add(*val1 as i32, *val2 as i32).1,
                ExpressionType::I16 => i16::overflowing_add(*val1 as i16, *val2 as i16).1,
                ExpressionType::I8 => i8::overflowing_add(*val1 as i8, *val2 as i8).1,
                _ => unreachable!("{:?}", target_type),
            }
            .into(),
            (ConstantDomain::U128(val1), ConstantDomain::U128(val2)) => match target_type {
                ExpressionType::Usize => usize::overflowing_add(*val1 as usize, *val2 as usize).1,
                ExpressionType::U128 => u128::overflowing_add(*val1, *val2).1,
                ExpressionType::U64 => u64::overflowing_add(*val1 as u64, *val2 as u64).1,
                ExpressionType::U32 => u32::overflowing_add(*val1 as u32, *val2 as u32).1,
                ExpressionType::U16 => u16::overflowing_add(*val1 as u16, *val2 as u16).1,
                ExpressionType::U8 => u8::overflowing_add(*val1 as u8, *val2 as u8).1,
                _ => unreachable!("{:?}", target_type),
            }
            .into(),
            _ => ConstantDomain::Bottom,
        }
    }
}

/// Keeps track of MIR constants that have already been mapped onto ConstantDomain instances.
pub struct ConstantValueCache {
    char_cache: HashMap<char, ConstantDomain>,
    function_cache: HashMap<DefId, ConstantDomain>,
    f32_cache: HashMap<u32, ConstantDomain>,
    f64_cache: HashMap<u64, ConstantDomain>,
    i128_cache: HashMap<i128, ConstantDomain>,
    u128_cache: HashMap<u128, ConstantDomain>,
    str_cache: HashMap<String, ConstantDomain>,
    core_slice_len_function: Option<ConstantDomain>,
    mirai_assume_function: Option<ConstantDomain>,
    mirai_precondition_function: Option<ConstantDomain>,
    mirai_verify_function: Option<ConstantDomain>,
    std_panicking_panic_function: Option<ConstantDomain>,
    heap_address_counter: usize,
}

impl ConstantValueCache {
    pub fn new() -> ConstantValueCache {
        ConstantValueCache {
            char_cache: HashMap::default(),
            function_cache: HashMap::default(),
            f32_cache: HashMap::default(),
            f64_cache: HashMap::default(),
            i128_cache: HashMap::default(),
            u128_cache: HashMap::default(),
            str_cache: HashMap::default(),
            core_slice_len_function: None,
            mirai_assume_function: None,
            mirai_precondition_function: None,
            mirai_verify_function: None,
            std_panicking_panic_function: None,
            heap_address_counter: 0,
        }
    }

    /// Returns a Expression::AbstractHeapAddress with a unique counter value.
    pub fn get_new_heap_address(&mut self) -> Expression {
        let heap_address_counter = self.heap_address_counter;
        self.heap_address_counter = self.heap_address_counter.wrapping_add(1);
        Expression::AbstractHeapAddress(heap_address_counter)
    }

    /// Returns a reference to a cached Expression::Char(value).
    pub fn get_char_for(&mut self, value: char) -> &ConstantDomain {
        self.char_cache
            .entry(value)
            .or_insert_with(|| ConstantDomain::Char(value))
    }

    /// Returns a reference to a cached Expression::F32(value).
    pub fn get_f32_for(&mut self, value: u32) -> &ConstantDomain {
        self.f32_cache
            .entry(value)
            .or_insert_with(|| ConstantDomain::F32(value))
    }

    /// Returns a reference to a cached Expression::F64(value).
    pub fn get_f64_for(&mut self, value: u64) -> &ConstantDomain {
        self.f64_cache
            .entry(value)
            .or_insert_with(|| ConstantDomain::F64(value))
    }

    /// Returns a reference to a cached Expression::I128(value).
    pub fn get_i128_for(&mut self, value: i128) -> &ConstantDomain {
        self.i128_cache
            .entry(value)
            .or_insert_with(|| ConstantDomain::I128(value))
    }

    pub fn get_string_for(&mut self, value: &str) -> &ConstantDomain {
        let str_value = String::from(value);
        self.str_cache
            .entry(str_value)
            .or_insert_with(|| ConstantDomain::Str(String::from(value)))
    }

    /// Returns a reference to a cached Expression::U128(value).
    pub fn get_u128_for(&mut self, value: u128) -> &ConstantDomain {
        self.u128_cache
            .entry(value)
            .or_insert_with(|| ConstantDomain::U128(value))
    }

    /// Given the MIR DefId of a function return the unique (cached) ConstantDomain that corresponds
    /// to the function identified by that DefId.
    pub fn get_function_constant_for(
        &mut self,
        def_id: DefId,
        tcx: &TyCtxt<'_, '_, '_>,
        summary_cache: &mut PersistentSummaryCache<'_, '_>,
    ) -> &ConstantDomain {
        self.function_cache
            .entry(def_id)
            .or_insert_with(|| ConstantDomain::for_function(def_id, tcx, summary_cache))
    }

    /// Does an expensive check to see if the given function is mirai_annotations.mirai_assume.
    /// Once it finds the function it caches it so that subsequent checks are cheaper.
    pub fn check_if_core_slice_len_function(&mut self, fun: &ConstantDomain) -> bool {
        let result = self
            .core_slice_len_function
            .as_ref()
            .map(|cached_fun| *cached_fun == *fun);
        result.unwrap_or_else(|| {
            let result = match fun {
                ConstantDomain::Function {
                    summary_cache_key, ..
                } => summary_cache_key == "core.slice.{{impl}}.len",
                _ => false,
            };
            if result {
                self.core_slice_len_function = Some(fun.clone());
            };
            result
        })
    }

    /// Does an expensive check to see if the given function is mirai_annotations.mirai_assume.
    /// Once it finds the function it caches it so that subsequent checks are cheaper.
    pub fn check_if_mirai_assume_function(&mut self, fun: &ConstantDomain) -> bool {
        let result = self
            .mirai_assume_function
            .as_ref()
            .map(|cached_fun| *cached_fun == *fun);
        result.unwrap_or_else(|| {
            let result = match fun {
                ConstantDomain::Function {
                    summary_cache_key, ..
                } => summary_cache_key.ends_with("mirai_annotations.mirai_assume"),
                _ => false,
            };
            if result {
                self.mirai_assume_function = Some(fun.clone());
            };
            result
        })
    }

    /// Does an expensive check to see if the given function is mirai_annotations.mirai_precondition.
    /// Once it finds the function it caches it so that subsequent checks are cheaper.
    pub fn check_if_mirai_precondition_function(&mut self, fun: &ConstantDomain) -> bool {
        let result = self
            .mirai_precondition_function
            .as_ref()
            .map(|cached_fun| *cached_fun == *fun);
        result.unwrap_or_else(|| {
            let result = match fun {
                ConstantDomain::Function {
                    summary_cache_key, ..
                } => summary_cache_key.ends_with("mirai_annotations.mirai_precondition"),
                _ => false,
            };
            if result {
                self.mirai_precondition_function = Some(fun.clone());
            };
            result
        })
    }

    /// Does an expensive check to see if the given function is mirai_annotations.mirai_verify.
    /// Once it finds the function it caches it so that subsequent checks are cheaper.
    pub fn check_if_mirai_verify_function(&mut self, fun: &ConstantDomain) -> bool {
        let result = self
            .mirai_verify_function
            .as_ref()
            .map(|cached_fun| *cached_fun == *fun);
        result.unwrap_or_else(|| {
            let result = match fun {
                ConstantDomain::Function {
                    summary_cache_key, ..
                } => summary_cache_key.ends_with("mirai_annotations.mirai_verify"),
                _ => false,
            };
            if result {
                self.mirai_verify_function = Some(fun.clone());
            };
            result
        })
    }

    /// Does an expensive check to see if the given function is std.panicking.begin_panic.
    /// Once it finds the function it caches it so that subsequent checks are cheaper.
    pub fn check_if_std_panicking_begin_panic_function(&mut self, fun: &ConstantDomain) -> bool {
        let result = self
            .std_panicking_panic_function
            .as_ref()
            .map(|std_fun| *std_fun == *fun);
        result.unwrap_or_else(|| {
            let result = match fun {
                ConstantDomain::Function {
                    summary_cache_key, ..
                } => summary_cache_key == "std.panicking.begin_panic",
                _ => false,
            };
            if result {
                self.std_panicking_panic_function = Some(fun.clone());
            };
            result
        })
    }
}

impl Default for ConstantValueCache {
    fn default() -> Self {
        Self::new()
    }
}
