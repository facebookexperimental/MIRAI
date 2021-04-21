// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//
// A test that checks that bit counting operations have return results that are constrained
// beyond their type signature.

use mirai_annotations::*;

pub fn t1(bit_map: u8) {
    let ones = bit_map.count_ones();
    verify!(ones < 9);
}

pub fn main() {}
