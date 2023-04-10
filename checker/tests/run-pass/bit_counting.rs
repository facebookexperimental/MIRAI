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

pub fn t2(mut existence_bitmap: u16) {
    for _ in 0..existence_bitmap.count_ones() {
        let next_child = existence_bitmap.trailing_zeros() as u8;
        assume!(next_child < 16); // because we'll only get here if existence_bitmap is not zero
        existence_bitmap &= !(1 << next_child);
    }
}

pub fn main() {}
