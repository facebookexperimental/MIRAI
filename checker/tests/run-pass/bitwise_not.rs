// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Tests reasoning over bitwise not operations

use mirai_annotations::*;

pub fn signed_arith(i: i8) {
    precondition!(!i < i8::max_value());
    let neg = !i + 1;
    verify!(neg == -i);
}

pub fn unsigned_arith(i: u8) {
    verify!(!i == 255 - i);
}

pub fn bits(i: u8) {
    precondition!(i & 1 == 0);
    verify!(!i & 1 != 0);
    verify!(!i & 1 == 1);
}

pub fn constants() {
    verify!(!0x11u8 == 0xeeu8);
    verify!(!0x11u8 as u128 == 0xeeu128);
    verify!(!0x11u128 == 0xffffffffffffffffffffffffffffffeeu128);
}

pub fn main() {}
