// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that core::cmp::max creates correct summaries

use mirai_annotations::*;

pub fn test_i8() {
    let val1: i8 = result!();
    let val2: i8 = result!();
    let result = core::cmp::max(val1, val2);
    verify!(result <= std::i8::MAX);
}

pub fn test_i16() {
    let val1: i16 = result!();
    let val2: i16 = result!();
    let result = core::cmp::max(val1, val2);
    verify!(result <= std::i16::MAX);
}

pub fn test_i32() {
    let val1: i32 = result!();
    let val2: i32 = result!();
    let result = core::cmp::max(val1, val2);
    verify!(result <= std::i32::MAX);
}

pub fn test_i64() {
    let val1: i64 = result!();
    let val2: i64 = result!();
    let result = core::cmp::max(val1, val2);
    verify!(result <= std::i64::MAX);
}

pub fn test_i128() {
    let val1: i128 = result!();
    let val2: i128 = result!();
    let result = core::cmp::max(val1, val2);
    verify!(result <= i128::MAX);
}

pub fn test_isize() {
    let val1: isize = result!();
    let val2: isize = result!();
    let result = core::cmp::max(val1, val2);
    verify!(result <= isize::MAX);
}

pub fn test_u8() {
    let val1: u8 = result!();
    let val2: u8 = result!();
    let result = core::cmp::max(val1, val2);
    verify!(result <= u8::MAX);
}

pub fn test_u16() {
    let val1: u16 = result!();
    let val2: u16 = result!();
    let result = core::cmp::max(val1, val2);
    verify!(result <= u16::MAX);
}

pub fn test_u32() {
    let val1: u32 = result!();
    let val2: u32 = result!();
    let result = core::cmp::max(val1, val2);
    verify!(result <= u32::MAX);
}

pub fn test_u64() {
    let val1: u64 = result!();
    let val2: u64 = result!();
    let result = core::cmp::max(val1, val2);
    verify!(result <= u64::MAX);
}

pub fn test_u128() {
    let val1: u128 = result!();
    let val2: u128 = result!();
    let result = core::cmp::max(val1, val2);
    verify!(result <= u128::MAX);
}

pub fn test_usize() {
    let val1: usize = result!();
    let val2: usize = result!();
    let result = core::cmp::max(val1, val2);
    verify!(result <= usize::MAX);
}

pub fn main() {}
