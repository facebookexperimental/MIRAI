// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test that infers preconditions that contain local variables and thus emit diagnostics

#[macro_use]
extern crate mirai_annotations;

fn test(v: &[i32]) {
    let mut i = 0;
    let n = v.len();
    while i < n {
        verify!(v[i] >= 0); //~ possible false verification condition
                            // todo: improve precondition promotion by e.g., supporting quantification
        i += 1;
    }
}

pub fn main() {
    let a = [-1, 2, 3];
    let b = [1, 2, 3];
    test(&a);
    test(&b);
}
