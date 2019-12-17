// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Tests constant folding of arithmetic binary operations that overflow

#[macro_use]
extern crate mirai_annotations;

pub fn tu8_add() -> u8 {
    let a: u8 = 255;
    a + 1 //~ attempt to add with overflow
}

pub fn tu8_sub() -> u8 {
    let a: u8 = 0;
    a - 1 //~ attempt to subtract with overflow
}

pub fn tu8_div() -> u8 {
    let a: u8 = 255;
    let b: u8 = 0;
    a / b //~ attempt to divide by zero
}

pub fn tu8_mul() -> u8 {
    let a: u8 = 255;
    a * 2 //~ attempt to multiply with overflow
}

pub fn tu8_overflowing_mul() {
    let a: u8 = 255;
    let (a2, it_overflows) = a.overflowing_mul(2);
    verify!(it_overflows);
    verify!(a2 == 254);
}
pub fn ti8_overflowing_mul() {
    let a: i8 = 127;
    let (a2, it_overflows) = a.overflowing_mul(2);
    verify!(it_overflows);
    verify!(a2 == -2); //~ possible false verification condition
}

pub fn tu128_overflowing_mul() {
    let a: u128 = std::u128::MAX;
    let (a2, it_overflows) = a.overflowing_mul(2);
    verify!(it_overflows);
    verify!(a2 == 340282366920938463463374607431768211454); //~ possible false verification condition
}

pub fn tu8_rem() -> u8 {
    let a: u8 = 255;
    let b: u8 = 0;
    a % b //~ attempt to calculate the remainder with a divisor of zero
}

pub fn tu8_shl() -> u8 {
    let a: u8 = 255;
    let b = 8;
    a << b //~ attempt to shift left with overflow
}

pub fn tu8_shr() -> u8 {
    let a: u8 = 255;
    let b = 8;
    a >> b //~ attempt to shift right with overflow
}

pub fn ti8_add() -> i8 {
    let a: i8 = 127;
    a + 1 //~ attempt to add with overflow
}

pub fn ti8_div0() -> i8 {
    let a: i8 = 127;
    let b: i8 = 0;
    a / b //~ attempt to divide by zero
}

pub fn ti8_div_m1() -> i8 {
    let a: i8 = -128;
    let b: i8 = -1;
    a / b //~ attempt to divide with overflow
}

pub fn ti8_mul() -> i8 {
    let a: i8 = 127;
    a * 2 //~ attempt to multiply with overflow
}

pub fn ti8_rem() -> i8 {
    let a: i8 = 127;
    let b: i8 = 0;
    a % b //~ attempt to calculate the remainder with a divisor of zero
}

pub fn ti8_rem_m1() -> i8 {
    let a: i8 = -128;
    let b: i8 = -1;
    a % b //~ attempt to calculate the remainder with overflow
}

pub fn ti8_shl() -> i8 {
    let a: i8 = 127;
    let b = 8;
    a << b //~ attempt to shift left with overflow
}

pub fn ti8_shr() -> i8 {
    let a: i8 = 127;
    let b = 8;
    a >> b //~ attempt to shift right with overflow
}

pub fn main() {}
