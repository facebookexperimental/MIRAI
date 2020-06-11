// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test for adding/checking tags on an array element

#![feature(const_generics)]
#![allow(incomplete_features)]

#[macro_use]
extern crate mirai_annotations;

use mirai_annotations::{TagPropagation, TagPropagationSet};

struct SecretTaintKind<const MASK: TagPropagationSet> {}

const SECRET_TAINT: TagPropagationSet = tag_propagation_set!(TagPropagation::BitOr);

type SecretTaint = SecretTaintKind<SECRET_TAINT>;

pub fn test(v: Vec<i32>, i: usize) {
    precondition!(i < v.len() && v.len() == 3);
    add_tag!(&v[i], SecretTaint);
    verify!(has_tag!(&v[i], SecretTaint));
    verify!(does_not_have_tag!(&v[0], SecretTaint)); // todo: implement weak updates for tags
}

pub fn main() {}
