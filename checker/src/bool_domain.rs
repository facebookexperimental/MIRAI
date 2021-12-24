// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use log_derive::logfn_inputs;
use serde::{Deserialize, Serialize};

/// A standard set-based abstraction for Booleans. `Bottom` represents the empty set,
/// `False` and `True` represent singleton sets {true} and {false}, respectively, and
/// `Top` represents {false, true}. This domain can be embedded into other domains,
/// such as the tag domain, which maps each tag to a Boolean domain element to record
/// whether the tag is present or not.
#[derive(Ord, PartialOrd, Eq, PartialEq, Debug, Copy, Clone, Serialize, Deserialize, Hash)]
pub enum BoolDomain {
    Bottom,
    False,
    True,
    Top,
}

impl From<bool> for BoolDomain {
    #[logfn_inputs(TRACE)]
    fn from(b: bool) -> BoolDomain {
        if b {
            BoolDomain::True
        } else {
            BoolDomain::False
        }
    }
}

/// Transfer functions
impl BoolDomain {
    /// Return the join of two Boolean domain elements, which is essentially the set union.
    #[logfn_inputs(TRACE)]
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            // [Top join _] -> Top
            // [False join True] -> Top
            (BoolDomain::Top, _)
            | (_, BoolDomain::Top)
            | (BoolDomain::False, BoolDomain::True)
            | (BoolDomain::True, BoolDomain::False) => BoolDomain::Top,

            // [False join False] -> False
            // [False join Bottom] -> False
            (BoolDomain::False, _) | (_, BoolDomain::False) => BoolDomain::False,

            // [True join True] -> True
            // [True join Bottom] -> True
            (BoolDomain::True, _) | (_, BoolDomain::True) => BoolDomain::True,

            // [Bottom join Bottom] -> Bottom
            (BoolDomain::Bottom, BoolDomain::Bottom) => BoolDomain::Bottom,
        }
    }

    /// Return the logical-or of two Boolean domain elements.
    #[logfn_inputs(TRACE)]
    #[must_use]
    pub fn or(&self, other: &Self) -> Self {
        match (self, other) {
            // [Bottom || _] -> Bottom
            (BoolDomain::Bottom, _) | (_, BoolDomain::Bottom) => BoolDomain::Bottom,

            // [True || True] -> True
            // [True || False] -> True
            // [True || Top] -> True
            (BoolDomain::True, _) | (_, BoolDomain::True) => BoolDomain::True,

            // [Top || Top] -> Top
            // [Top || False] -> Top
            (BoolDomain::Top, _) | (_, BoolDomain::Top) => BoolDomain::Top,

            // [False || False] -> False
            (BoolDomain::False, BoolDomain::False) => BoolDomain::False,
        }
    }
}
