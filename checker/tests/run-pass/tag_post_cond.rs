// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test for taint tags that flow from components to containers

#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

use mirai_annotations::*;

struct SecretTaintKind<const MASK: TagPropagationSet> {}

const SECRET_TAINT: TagPropagationSet = tag_propagation_set!(TagPropagation::SuperComponent);

type SecretTaint = SecretTaintKind<SECRET_TAINT>;

pub struct A(u32);

pub struct B(u32);

pub fn a_to_b(a: A) -> B {
    precondition!(has_tag!(&a, SecretTaint));
    let b = B(a.0);
    postcondition!(has_tag!(&b, SecretTaint));
    b
}

pub fn main() {
    let a = A(1);
    add_tag!(&a.0, SecretTaint);
    let b = a_to_b(a);
    verify!(has_tag!(&b, SecretTaint));
}
