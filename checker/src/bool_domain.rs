// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use log_derive::logfn_inputs;

/// A standard set-based abstraction for Booleans. `Bottom` represents the empty set,
/// `False` and `True` represent singleton sets {true} and {false}, respectively, and
/// `Top` represents {false, true}. This domain can be embedded into other domains,
/// such as the tag domain, which maps each tag to a Boolean domain element to record
/// whether the tag is present or not.
#[derive(Ord, PartialOrd, Eq, PartialEq, Debug, Copy, Clone)]
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
