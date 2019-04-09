// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

use crate::expression::ExpressionType::{self, *};

use serde::{Deserialize, Serialize};
use std::cmp;
use std::convert::TryFrom;

/// An element of the Interval domain is a range of i128 numbers denoted by a lower bound and
/// upper bound. A lower bound of std::i128::MIN denotes -infinity and an upper bound of
/// std::i128::MAX denotes +infinity.
/// Interval domain elements are constructed on demand from AbstractDomain expressions.
/// They are most useful for checking if an array index is within bounds.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialOrd, PartialEq, Hash, Ord)]
pub struct IntervalDomain {
    lower_bound: i128,
    upper_bound: i128,
}

pub const BOTTOM: IntervalDomain = IntervalDomain {
    lower_bound: 1,
    upper_bound: 0,
};

pub const TOP: IntervalDomain = IntervalDomain {
    lower_bound: std::i128::MIN,
    upper_bound: std::i128::MAX,
};

impl From<i128> for IntervalDomain {
    fn from(i: i128) -> IntervalDomain {
        IntervalDomain {
            lower_bound: i,
            upper_bound: i,
        }
    }
}

impl From<u128> for IntervalDomain {
    fn from(u: u128) -> IntervalDomain {
        if let Result::Ok(i) = i128::try_from(u) {
            i.into()
        } else {
            IntervalDomain {
                lower_bound: std::i128::MAX,
                upper_bound: std::i128::MAX,
            }
        }
    }
}

impl IntervalDomain {
    //[x...y] + [a...b] = [x+a...y+b]
    pub fn add(&self, other: &Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return BOTTOM.clone();
        }
        if self.is_top() || other.is_top() {
            return TOP.clone();
        }
        IntervalDomain {
            lower_bound: self.lower_bound.saturating_add(other.lower_bound),
            upper_bound: self.upper_bound.saturating_add(other.upper_bound),
        }
    }

    // [x...y] >= [a...b] = x >= b
    // !([x...y] >= [a...b]) = [a...b] > [x...y] = a > y
    pub fn greater_or_equal(&self, other: &Self) -> Option<bool> {
        if self.is_bottom() || self.is_top() || other.is_bottom() || other.is_top() {
            None
        } else if self.lower_bound >= other.upper_bound {
            Some(true)
        } else if other.lower_bound > self.upper_bound {
            Some(false)
        } else {
            None
        }
    }

    // [x...y] > [a...b] = x > b
    // !([x...y] > [a...b]) = [a...b] >= [x...y] = a >= y
    pub fn greater_than(&self, other: &Self) -> Option<bool> {
        if self.is_bottom() || self.is_top() || other.is_bottom() || other.is_top() {
            None
        } else if self.lower_bound > other.upper_bound {
            Some(true)
        } else if other.lower_bound >= self.upper_bound {
            Some(false)
        } else {
            None
        }
    }

    // The expression that corresponds to this interval is not known to result in a integer value.
    // This is either because we just don't know, or because the necessary transfer function was
    // not implemented. The expectation is that bottom values will not often be encountered.
    // We don't need this domain to implement transfer functions for all operations that might
    // result in integer values since other domains will be preferred in those cases.
    pub fn is_bottom(&self) -> bool {
        self.upper_bound < self.lower_bound
    }

    // Returns true if this interval is known to be contained in the interval [target_type::MIN ... target_type::MAX].
    // A false result just means that we don't know, it never means that we know it does not.
    // Note that i128::MIN and i128::MAX are reserved to indicate missing (unbounded) lower and upper
    // bounds, respectively.
    pub fn is_contained_in(&self, target_type: &ExpressionType) -> bool {
        if self.is_bottom() || self.is_top() {
            return false;
        };
        match target_type {
            I8 => {
                self.lower_bound >= i128::from(std::i8::MIN)
                    && self.upper_bound <= i128::from(std::i8::MAX)
            }
            I16 => {
                self.lower_bound >= i128::from(std::i16::MIN)
                    && self.upper_bound <= i128::from(std::i16::MAX)
            }
            I32 => {
                self.lower_bound >= i128::from(std::i32::MIN)
                    && self.upper_bound <= i128::from(std::i32::MAX)
            }
            I64 => {
                self.lower_bound >= i128::from(std::i64::MIN)
                    && self.upper_bound <= i128::from(std::i64::MAX)
            }
            I128 => self.lower_bound > std::i128::MIN && self.upper_bound < std::i128::MAX,
            Isize => {
                self.lower_bound >= (std::isize::MIN as i128)
                    && self.upper_bound <= (std::isize::MAX as i128)
            }
            U8 => self.lower_bound >= 0 && self.upper_bound <= i128::from(std::u8::MAX),
            U16 => self.lower_bound >= 0 && self.upper_bound <= i128::from(std::u16::MAX),
            U32 => self.lower_bound >= 0 && self.upper_bound <= i128::from(std::u32::MAX),
            U64 => self.lower_bound >= 0 && self.upper_bound <= i128::from(std::u64::MAX),
            U128 => self.lower_bound >= 0 && self.upper_bound < std::i128::MAX,
            Usize => self.lower_bound >= 0 && self.upper_bound <= (std::usize::MAX as i128),
            _ => false,
        }
    }

    // Returns true if this interval is known to be contained in the interval [0 ... bit size of target_type).
    // A false result just means that we don't know, it never means that we know it does not.
    pub fn is_contained_in_width_of(&self, target_type: &ExpressionType) -> bool {
        if self.is_bottom() || self.is_top() {
            return false;
        };
        match target_type {
            I8 | U8 => self.lower_bound >= 0 && self.upper_bound < 8,
            I16 | U16 => self.lower_bound >= 0 && self.upper_bound < 16,
            I32 | U32 => self.lower_bound >= 0 && self.upper_bound < 32,
            I64 | U64 => self.lower_bound >= 0 && self.upper_bound < 64,
            I128 | U128 => self.lower_bound >= 0 && self.upper_bound < 128,
            Isize | Usize => {
                self.lower_bound >= 0 && self.upper_bound < i128::from(std::usize::MAX.count_ones())
            }
            _ => false,
        }
    }

    // All concrete integer values belong to this interval, so we know nothing.
    pub fn is_top(&self) -> bool {
        self.lower_bound == std::i128::MIN && self.upper_bound == std::i128::MAX
    }

    // [x...y] <= [a...b] = y <= a
    // !([x...y] <= [a...b]) = [a...b] < [x...y] = b < x
    pub fn less_equal(&self, other: &Self) -> Option<bool> {
        if self.is_bottom() || self.is_top() || other.is_bottom() || other.is_top() {
            None
        } else if self.upper_bound <= other.lower_bound {
            Some(true)
        } else if other.upper_bound < self.lower_bound {
            Some(false)
        } else {
            None
        }
    }

    // [x...y] < [a...b] = y < a
    // !([x...y] < [a...b]) = [a...b] <= [x...y] = b <= x
    pub fn less_than(&self, other: &Self) -> Option<bool> {
        if self.is_bottom() || self.is_top() || other.is_bottom() || other.is_top() {
            None
        } else if self.upper_bound < other.lower_bound {
            Some(true)
        } else if other.upper_bound <= self.lower_bound {
            Some(false)
        } else {
            None
        }
    }

    pub fn lower_bound(&self) -> Option<i128> {
        if self.lower_bound == TOP.lower_bound {
            None
        } else {
            Some(self.lower_bound)
        }
    }

    pub fn upper_bound(&self) -> Option<i128> {
        if self.upper_bound == TOP.upper_bound {
            None
        } else {
            Some(self.upper_bound)
        }
    }

    pub fn remove_lower_bound(&self) -> Self {
        IntervalDomain {
            lower_bound: TOP.lower_bound,
            upper_bound: self.upper_bound,
        }
    }

    pub fn remove_upper_bound(&self) -> Self {
        IntervalDomain {
            lower_bound: self.lower_bound,
            upper_bound: TOP.upper_bound,
        }
    }

    // [x...y] * [a...b] = [x*a...y*b]
    pub fn mul(&self, other: &Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return BOTTOM.clone();
        }
        if self.is_top() || other.is_top() {
            return TOP.clone();
        }
        IntervalDomain {
            lower_bound: self.lower_bound.saturating_mul(other.lower_bound),
            upper_bound: self.upper_bound.saturating_mul(other.upper_bound),
        }
    }

    // -[x...y] = [-y...-x]
    pub fn neg(&self) -> Self {
        if self.is_bottom() {
            return BOTTOM.clone();
        }
        if self.is_top() {
            return TOP.clone();
        }
        IntervalDomain {
            lower_bound: self.upper_bound.checked_neg().unwrap_or(std::i128::MAX),
            upper_bound: self.lower_bound.checked_neg().unwrap_or(std::i128::MAX),
        }
    }

    // [x...y] - [a...b] = [x-b...y-a]
    pub fn sub(&self, other: &Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return BOTTOM.clone();
        }
        if self.is_top() || other.is_top() {
            return TOP.clone();
        }
        IntervalDomain {
            lower_bound: self.lower_bound.saturating_sub(other.upper_bound),
            upper_bound: self.upper_bound.saturating_sub(other.lower_bound),
        }
    }

    // [x...y] widen [a...b] = [min(x,a)...max(y,b)],
    pub fn widen(&self, other: &Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return BOTTOM.clone();
        }
        if self.is_top() || other.is_top() {
            return TOP.clone();
        }
        IntervalDomain {
            lower_bound: cmp::min(self.lower_bound, other.lower_bound),
            upper_bound: cmp::max(self.upper_bound, other.upper_bound),
        }
    }
}
