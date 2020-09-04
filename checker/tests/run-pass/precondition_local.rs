// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test that infers a precondition from a loop invariant

#[macro_use]
extern crate mirai_annotations;

fn test(v: &[i32]) {
    let mut i = 0;
    let n = v.len();
    while i < n {
        verify!(v[i] >= 0); //~ related location
        i += 1;
    }
}

pub fn main() {
    //todo: avoid "possible possible"
    let a = [-1, 2, 3]; //~ possible possible false verification condition
    let b = [1, 2, 3];
    test(&a);
    test(&b);
}
