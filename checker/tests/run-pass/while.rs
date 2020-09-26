// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that increments a counter inside a while loop

use mirai_annotations::*;

pub fn foo(n: usize) {
    let mut i: usize = 0;
    while i < n {
        verify!(i < n);
        i += 1;
    }
    verify!(i >= n);
}

pub fn bar(n: usize) {
    let mut i: usize = 10;
    while i > n {
        verify!(i > n);
        i -= 1;
    }
    verify!(i <= n);
}

pub fn main() {}
