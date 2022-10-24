// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

use mirai_annotations::*;

// MIRAI_FLAGS --test_only

#[test]
fn some_test() {
    verify!(1 == 1);
}

#[test]
fn another_test() {
    // todo: fix this
    verify!(2 == 1); // ~ provably false verification condition
}

pub fn main() {
    // Should not complain because it is not a test function and therefore not analyzed.
    verify!(2 == 1);
}
