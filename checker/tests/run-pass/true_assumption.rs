// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a true assumption
// MIRAI_FLAGS -- -Z mir-opt-level=0

use mirai_annotations::*;

pub fn test_assume() {
    let i = 1;
    assume!(i == 1); //~ assumption is provably true and can be deleted
}

pub fn test_unreachable_assume() {
    let i = 1;
    if i != 1 {
        assume!(i == 1); //~ this is unreachable, mark it as such by using the verify_unreachable! macro
    }
}

pub fn main() {}
