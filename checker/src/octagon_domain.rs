// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

use crate::expression::ExpressionType::{self, *};
use log_derive::logfn_inputs;
use serde::{Deserialize, Serialize};
use std::cmp;
use std::convert::TryFrom;

/// An element of the Octagon domain is a Distance-Bound Matrix(DBM) of size 4x4.
/// Each cell of the matrix represents potential constraint of the form Vi-Vj<=c,
/// where c is some constant, Vi and Vj are variables. 
/// For instance, DBM can be represented as follows 
///   | V1 |  V2 |  V3 |  V4 |
/// V1|  0 | -10 |  -5 |  15 |
/// V2| 10 |   0 | -15 |   5 |
/// V3| -5 |  15 |   0 | -20 |
/// V4| 15 |   5 |  20 |   0 |
///
/// The matrix has twice more columns and rows because each variable represents
/// positive and negative values in the constraints. More specifically, V2i-1 is
/// a positive value, V2i is a negative one. In other words, if at some point 
/// of the static analysis some variable x has been encountered, V1 would 
/// represent +x values while V2 -x ones. Thus, the constraint V2-V1<=-10 can be
/// represented as x >=-5.
/// Octagon domain elements are constructed on demand from AbstractDomain expressions.
/// They are useful in places where the Interval domain is not precise enough. For
/// example, in the code below the Interval domain will give y=[0;+inf] precision,
/// while the Octagon domain - y=[0;4]
/// ```
/// let x = 0; let y = 0;
/// while x < 4 {
///     x += 1;
///     y = if random() { y + 1 };
/// } 
/// ```
#[derive(Serialize, Deserialize, Clone, Eq, PartialOrd, PartialEq, Hash, Ord)]
pub struct OctagonDomain {
    dbm: [[i128; 4]; 4],
}

impl std::fmt::Debug for OctagonDomain {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:?}", self.dbm))
    }
}

pub const BOTTOM: OctagonDomain = OctagonDomain {
    dbm: [[0i128; 4]; 4],
};

pub const TOP: OctagonDomain = {
    let mut dbm = [[0i128; 4]; 4];
    dbm[0][1] = std::i128::MIN;
    dbm[1][0] = std::i128::MAX;
    OctagonDomain {
        dbm
    }
};

impl From<i128> for OctagonDomain {
    #[logfn_inputs(TRACE)]
    fn from(i: i128) -> OctagonDomain {
        OctagonDomain::new(i, i)
    }
}

impl From<u128> for OctagonDomain {
    #[logfn_inputs(TRACE)]
    fn from(u: u128) -> OctagonDomain {
        if let Result::Ok(i) = i128::try_from(u) {
            i.into()
        } else {
            OctagonDomain::new(std::i128::MAX, std::i128::MAX)
        }
    }
}

impl OctagonDomain {
    pub fn new(left: i128, right: i128) -> Self {
        let mut dbm = [[0i128; 4]; 4];
        dbm[0][1] = left;
        dbm[1][0] = right;
        OctagonDomain {
            dbm
        }
    }

    #[logfn_inputs(TRACE)]
    pub fn is_bottom(&self) -> bool {
        false
    }

    #[logfn_inputs(TRACE)]
    pub fn is_top(&self) -> bool {
        false
    }

    #[logfn_inputs(TRACE)]
    pub fn add(&self, other: &Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return BOTTOM.clone();
        }
        if self.is_top() || other.is_top() {
            return TOP.clone();
        }
        let left = self.dbm[0][1].saturating_add(other.dbm[0][1]);
        let right = self.dbm[1][0].saturating_add(other.dbm[1][0]);
        OctagonDomain::new(left, right)
    }

    #[logfn_inputs(TRACE)]
    pub fn greater_or_equal(&self, other: &Self) -> Option<bool> {
        if self.is_bottom() || self.is_top() || other.is_bottom() || other.is_top() {
            None
        } else if self.dbm[0][1] >= other.dbm[1][0] {
            Some(true)
        } else if other.dbm[0][1] > self.dbm[1][0] {
            Some(false)
        } else {
            None
        }
    }

    #[logfn_inputs(TRACE)]
    pub fn greater_than(&self, other: &Self) -> Option<bool> {
        if self.is_bottom() || self.is_top() || other.is_bottom() || other.is_top() {
            None
        } else if self.dbm[0][1] > other.dbm[1][0] {
            Some(true)
        } else if other.dbm[0][1] >= self.dbm[1][0] {
            Some(false)
        } else {
            None
        }
    }


    #[logfn_inputs(TRACE)]
    pub fn mul(&self, other: &Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return BOTTOM.clone();
        }
        if self.is_top() || other.is_top() {
            return TOP.clone();
        }
        let left = self.dbm[0][1].saturating_mul(other.dbm[0][1]);
        let right = self.dbm[1][0].saturating_mul(other.dbm[1][0]);
        OctagonDomain::new(left, right)
    }

    #[logfn_inputs(TRACE)]
    pub fn is_contained_in(&self, target_type: &ExpressionType) -> bool {
        if self.is_bottom() || self.is_top() {
            return false;
        };
        match target_type {
            I8 => {
                self.dbm[0][1] >= i128::from(std::i8::MIN)
                    && self.dbm[1][0] <= i128::from(std::i8::MAX)
            }
            I16 => {
                self.dbm[0][1] >= i128::from(std::i16::MIN)
                    && self.dbm[1][0] <= i128::from(std::i16::MAX)
            }
            I32 => {
                self.dbm[0][1] >= i128::from(std::i32::MIN)
                    && self.dbm[1][0] <= i128::from(std::i32::MAX)
            }
            I64 => {
                self.dbm[0][1] >= i128::from(std::i64::MIN)
                    && self.dbm[1][0] <= i128::from(std::i64::MAX)
            }
            I128 => self.dbm[0][1] > std::i128::MIN && self.dbm[1][0] < std::i128::MAX,
            Isize => {
                self.dbm[0][1] >= (std::isize::MIN as i128)
                    && self.dbm[1][0] <= (std::isize::MAX as i128)
            }
            U8 => self.dbm[0][1] >= 0 && self.dbm[1][0] <= i128::from(std::u8::MAX),
            U16 => self.dbm[0][1] >= 0 && self.dbm[1][0] <= i128::from(std::u16::MAX),
            U32 => self.dbm[0][1] >= 0 && self.dbm[1][0] <= i128::from(std::u32::MAX),
            U64 => self.dbm[0][1] >= 0 && self.dbm[1][0] <= i128::from(std::u64::MAX),
            U128 => self.dbm[0][1] >= 0 && self.dbm[1][0] < std::i128::MAX,
            Usize => self.dbm[0][1] >= 0 && self.dbm[1][0] <= (std::usize::MAX as i128),
            _ => false,
        }
    }

    #[logfn_inputs(TRACE)]
    pub fn is_contained_in_width_of(&self, target_type: &ExpressionType) -> bool {
        if self.is_bottom() || self.is_top() {
            return false;
        };
        match target_type {
            I8 | U8 => self.dbm[0][1] >= 0 && self.dbm[1][0] < 8,
            I16 | U16 => self.dbm[0][1] >= 0 && self.dbm[1][0] < 16,
            I32 | U32 => self.dbm[0][1] >= 0 && self.dbm[1][0] < 32,
            I64 | U64 => self.dbm[0][1] >= 0 && self.dbm[1][0] < 64,
            I128 | U128 => self.dbm[0][1] >= 0 && self.dbm[1][0] < 128,
            Isize | Usize => {
                self.dbm[0][1] >= 0 && self.dbm[1][0] < i128::from(std::usize::MAX.count_ones())
            }
            _ => false,
        }
    }

    
    #[logfn_inputs(TRACE)]
    pub fn less_equal(&self, other: &Self) -> Option<bool> {
        if self.is_bottom() || self.is_top() || other.is_bottom() || other.is_top() {
            None
        } else if self.dbm[1][0] <= other.dbm[0][1] {
            Some(true)
        } else if other.dbm[1][0] < self.dbm[0][1] {
            Some(false)
        } else {
            None
        }
    }

    #[logfn_inputs(TRACE)]
    pub fn less_than(&self, other: &Self) -> Option<bool> {
        if self.is_bottom() || self.is_top() || other.is_bottom() || other.is_top() {
            None
        } else if self.dbm[1][0] < other.dbm[0][1] {
            Some(true)
        } else if other.dbm[1][0] <= self.dbm[0][1] {
            Some(false)
        } else {
            None
        }
    }


    #[logfn_inputs(TRACE)]
    pub fn neg(&self) -> Self {
        if self.is_bottom() {
            return BOTTOM.clone();
        }
        if self.is_top() {
            return TOP.clone();
        }
        let left = self.dbm[0][1].checked_neg().unwrap_or(std::i128::MAX);
        let right = self.dbm[1][0].checked_neg().unwrap_or(std::i128::MAX);
        OctagonDomain::new(right, left)
    }

    #[logfn_inputs(TRACE)]
    pub fn sub(&self, other: &Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return BOTTOM.clone();
        }
        if self.is_top() || other.is_top() {
            return TOP.clone();
        }
        let left = self.dbm[0][1].saturating_sub(other.dbm[0][1]);
        let right = self.dbm[1][0].saturating_sub(other.dbm[1][0]);
        OctagonDomain::new(left, right)
    }

    #[logfn_inputs(TRACE)]
    pub fn widen(&self, other: &Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return BOTTOM.clone();
        }
        if self.is_top() || other.is_top() {
            return TOP.clone();
        }

        let left = cmp::min(self.dbm[0][1], other.dbm[0][1]);
        let right = cmp::max(self.dbm[1][0], other.dbm[1][0]);
        OctagonDomain::new(left, right)
    }
}
