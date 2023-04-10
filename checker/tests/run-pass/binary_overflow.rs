// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Tests constant folding of arithmetic binary operations that overflow
#![allow(arithmetic_overflow)]
#![allow(unconditional_panic)]

use mirai_annotations::*;

pub fn tu8_overflowing_mul() {
    let a: u8 = 255;
    let (_a2, it_overflows) = a.overflowing_mul(2);
    verify!(it_overflows);
    //verify!(a2 == 254);
}
pub fn ti8_overflowing_mul() {
    let a: i8 = 127;
    let (_a2, it_overflows) = a.overflowing_mul(2);
    verify!(it_overflows);
    //verify!(a2 == -2);
}

pub fn tu128_overflowing_mul() {
    let a: u128 = std::u128::MAX;
    let (_a2, it_overflows) = a.overflowing_mul(2);
    verify!(it_overflows);
    //verify!(a2 == 340282366920938463463374607431768211454);
}

pub fn ti8_div_m1() -> i8 {
    let a: i8 = -128;
    let b: i8 = -1;
    a / b //~ attempt to divide with overflow
}

pub fn ti8_rem_m1() -> i8 {
    let a: i8 = -128;
    let b: i8 = -1;
    a % b //~ attempt to calculate the remainder with overflow
}

pub fn main() {}
