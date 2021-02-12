// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test for transmutation of floating point numbers to integers

use mirai_annotations::*;

pub fn t1() {
    verify!((12.5f64).to_bits() == 0x4029000000000000);
}

pub fn main() {}
