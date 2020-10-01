// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that increments a parameter inside a while loop

use mirai_annotations::*;

pub fn foo(v: &[i32], i: usize) {
    precondition!(i <= v.len());
    let n = v.len();
    let mut j = i;
    while j < n {
        j += 1;
    }
    // todo: need some extra mechanism (such as narrowing) to prove the equality
    // verify!(j == n);
    verify!(j >= n);
}

pub fn bar(v: &[i32], mut i: usize) {
    precondition!(i < v.len());
    let n = v.len();
    while i < n {
        i += 1;
    }
    verify!(i >= n);
}

pub fn main() {}
