// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Tests constant folding of arithmetic binary operations that overflow

pub fn tu8_add() -> u8 {
    let a: u8 = 255;
    a + 1 //~ Control might reach this expression with operand values that cause a panic.
}

pub fn tu8_div() -> u8 {
    let a: u8 = 255;
    let b: u8 = 0;
    a / b    //~ Control might reach this expression with operand values that cause a panic.
}

pub fn tu8_mul() -> u8 {
    let a: u8 = 255;
    a * 2 //~ Control might reach this expression with operand values that cause a panic.
}

pub fn tu8_rem() -> u8 {
    let a: u8 = 255;
    let b: u8 = 0;
    a % b    //~ Control might reach this expression with operand values that cause a panic.
}

pub fn tu8_shl() -> u8 {
    let a: u8 = 255;
    let b = 8;
    a << b //~ Control might reach this expression with operand values that cause a panic.
}

pub fn tu8_shr() -> u8 {
    let a: u8 = 255;
    let b = 8;
    a >> b //~ Control might reach this expression with operand values that cause a panic.
}

pub fn ti8_add() -> i8 {
    let a: i8 = 127;
    a + 1 //~ Control might reach this expression with operand values that cause a panic.
}

pub fn ti8_div0() -> i8 {
    let a: i8 = 127;
    let b: i8 = 0;
    a / b    //~ Control might reach this expression with operand values that cause a panic.
}

pub fn ti8_div_m1() -> i8 {
    let a: i8 = -128;
    let b: i8 = -1;
    a / b    //~ Control might reach this expression with operand values that cause a panic.
}

pub fn ti8_mul() -> i8 {
    let a: i8 = 127;
    a * 2 //~ Control might reach this expression with operand values that cause a panic.
}

pub fn ti8_rem() -> i8 {
    let a: i8 = 127;
    let b: i8 = 0;
    a % b    //~ Control might reach this expression with operand values that cause a panic.
}

pub fn ti8_rem_m1() -> i8 {
    let a: i8 = -128;
    let b: i8 = -1;
    a % b    //~ Control might reach this expression with operand values that cause a panic.
}

pub fn ti8_shl() -> i8 {
    let a: i8 = 127;
    let b = 8;
    a << b //~ Control might reach this expression with operand values that cause a panic.
}

pub fn ti8_shr() -> i8 {
    let a: i8 = 127;
    let b = 8;
    a >> b //~ Control might reach this expression with operand values that cause a panic.
}
