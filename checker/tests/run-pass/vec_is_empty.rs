// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses inferred contracts for the Vec struct.

use mirai_annotations::*;

fn foo(a: &[i32]) -> i32 {
    precondition!(!a.is_empty());
    a[0]
}

pub fn main() {
    let v: Vec<i32> = Vec::new();
    verify!(v.is_empty());
    let a: [i32; 1] = [0];
    verify!(foo(&a) == 0);
}
