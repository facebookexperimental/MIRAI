// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree

// This is an example of using tag analysis to verify constant-time security.
// Use the following flag of MIRAI to enable constant-time verification:
// MIRAI_FLAGS --constant_time SecretTaintKind

#![cfg_attr(mirai, allow(incomplete_features), feature(generic_const_exprs))]

#[macro_use]
extern crate mirai_annotations;

#[cfg(mirai)]
use mirai_annotations::{TagPropagation, TagPropagationSet};

#[cfg(mirai)]
struct SecretTaintKind<const MASK: TagPropagationSet> {}

#[cfg(mirai)]
const SECRET_TAINT_MASK: TagPropagationSet = tag_propagation_set!(
    TagPropagation::Equals,
    TagPropagation::GreaterThan,
    TagPropagation::GreaterOrEqual,
    TagPropagation::LessThan,
    TagPropagation::LessOrEqual,
    TagPropagation::Ne
);

#[cfg(mirai)]
type SecretTaint = SecretTaintKind<SECRET_TAINT_MASK>;
#[cfg(not(mirai))]
type SecretTaint = ();

const KEY_LENGTH: usize = 1024;

pub mod non_constant_time {
    /// A compare function that is **not** constant-time.
    pub fn compare(secret: &[i32; crate::KEY_LENGTH], public: &[i32; crate::KEY_LENGTH]) -> bool {
        precondition!(has_tag!(secret, crate::SecretTaint));

        let mut i = 0;
        while i < crate::KEY_LENGTH {
            if secret[i] != public[i] {
                return false;
            }
            //~ the branch condition may have a SecretTaintKind tag
            i += 1;
        }
        true
    }
}

pub mod constant_time {
    /// A compare function that is constant-time.
    pub fn compare(secret: &[i32; crate::KEY_LENGTH], public: &[i32; crate::KEY_LENGTH]) -> bool {
        precondition!(has_tag!(secret, crate::SecretTaint));

        let mut result = true;
        let mut i = 0;
        while i < crate::KEY_LENGTH {
            result &= secret[i] == public[i];
            i += 1;
        }
        result
    }
}
