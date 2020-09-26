// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses an inferred post condition.

use mirai_annotations::*;

fn check_index(a: &[i64], i: usize) -> Option<usize> {
    if i < a.len() {
        Some(i)
    } else {
        None
    }
}

pub fn foo(i: usize) {
    if let Some(j) = check_index(&[0; 100], i) {
        verify!(j < 100);
    }
}

pub fn main() {}
