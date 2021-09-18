// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test for adding/checking tags on an array element

#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

use mirai_annotations::*;

struct SecretTaintKind<const MASK: TagPropagationSet> {}

const SECRET_TAINT: TagPropagationSet = tag_propagation_set!(TagPropagation::BitOr);

type SecretTaint = SecretTaintKind<SECRET_TAINT>;

pub fn test1(i: usize) {
    precondition!(i < 3usize);
    let v = [1, 2, 3];
    add_tag!(&v[i], SecretTaint);
    verify!(has_tag!(&v[i], SecretTaint));
    verify!(has_tag!(&v[0], SecretTaint)); //~ possible false verification condition
}

pub fn test2(i: usize) {
    precondition!(i < 3usize);
    let v = [1, 2, 3];
    add_tag!(&v[0], SecretTaint);
    verify!(has_tag!(&v[0], SecretTaint));
    verify!(does_not_have_tag!(&v[1], SecretTaint));
    verify!(has_tag!(&v[i], SecretTaint)); //~ possible false verification condition
}

pub fn test3(v: &[i32], i: usize) {
    precondition!(i < v.len() && v.len() == 3);
    add_tag!(&v[i], SecretTaint);
    verify!(has_tag!(&v[i], SecretTaint));
    verify!(has_tag!(&v[0], SecretTaint)); //~ possible false verification condition
}

pub fn main() {}
