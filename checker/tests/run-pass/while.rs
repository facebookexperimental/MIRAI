// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that increments a counter inside a while loop

pub fn foo(n: usize) {
    let mut i: usize = 0;
    while i < n {
        i += 1;
    }
}

pub fn bar(n: usize) {
    let mut i: usize = 10;
    while i > n {
        i -= 1;
    }
}

pub fn main() {}
