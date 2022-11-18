// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// MIRAI_FLAGS --diag=default

// A test that calls a function with a false precondition unconditionally from an analysis root

#![cfg_attr(mirai, allow(incomplete_features), feature(generic_const_exprs))]

use mirai_annotations::*;

struct SecretTaintKind<const MASK: TagPropagationSet> {}
const MASK: TagPropagationSet = TAG_PROPAGATION_ALL;
type SecretTaint = SecretTaintKind<MASK>;

fn foo(v: &Vec<i32>) {
    // This precondition should never be true.
    precondition!(does_not_have_tag!(&v[0], SecretTaint) && has_tag!(&v[0], SecretTaint));
    // ~ related location
}

pub fn main() {
    let v = vec![1, 2, 3];
    add_tag!(&v, SecretTaint);
    // todo: fix this
    foo(&v); // ~ unsatisfied precondition
}
