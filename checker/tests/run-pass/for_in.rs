// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a loop counter incremented via a for-in.

pub fn foo(n: usize) {
    for ordinal in 2..=n {
        assert!(ordinal - 1 >= 1); //~ possible attempt to subtract with overflow
    }
}

pub fn main() {}
