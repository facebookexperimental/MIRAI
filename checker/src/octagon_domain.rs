// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

use crate::expression::ExpressionType::{self, *};
use log_derive::logfn_inputs;
use serde::{Deserialize, Serialize};
use std::cmp;
//use std::convert::TryFrom;

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

    //[x...y] + [a...b] = [x+a...y+b]
    // TODO: update comment
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

    // [x...y] >= [a...b] = x >= b
    // !([x...y] >= [a...b]) = [a...b] > [x...y] = a > y
    // TODO: update comment
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

    // [x...y] > [a...b] = x > b
    // !([x...y] > [a...b]) = [a...b] >= [x...y] = a >= y
    // TODO: update comment
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


    // [x...y] * [a...b] = [x*a...y*b]
    // TODO: update comment
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

    // TODO: add doc
    // revise the method. The type should be within 2d dimentions, right? if so, I need to add more
    // rules
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

    
    // [x...y] <= [a...b] = y <= a
    // !([x...y] <= [a...b]) = [a...b] < [x...y] = b < x
    // TODO: update doc 
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

    // [x...y] < [a...b] = y < a
    // !([x...y] < [a...b]) = [a...b] <= [x...y] = b <= x
    // TODO: update doc 
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


    // -[x...y] = [-y...-x]
    // TODO: update doc 
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

    // [x...y] - [a...b] = [x-b...y-a]
    // TODO: update doc
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

    // [x...y] widen [a...b] = [min(x,a)...max(y,b)],
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
