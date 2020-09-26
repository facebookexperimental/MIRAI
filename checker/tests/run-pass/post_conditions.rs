// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses an explicit post condition.

use mirai_annotations::*;

pub struct Block {
    round: u64,
}

pub fn round(bl: Block) -> u64 {
    let result = bl.round;
    assumed_postcondition!(result < std::u64::MAX - 1);
    result
}

pub fn foo(bl: Block) {
    let ret = round(bl);
    verify!(ret < std::u64::MAX - 1);
}

pub fn non_joinable_post(c: bool) -> u64 {
    let result = result!();
    if c {
        //~ multiple post conditions must be on the same execution path
        assumed_postcondition!(result < 5);
    } else {
        assumed_postcondition!(result > 10);
    }
    result
}

pub fn joinable_post() -> u64 {
    let result = result!();
    assumed_postcondition!(result > 0);
    assumed_postcondition!(result < 10);
    assumed_postcondition!(result % 2 == 0);
    result
}

pub fn test_joinable_post() {
    let x = joinable_post();
    verify!(x > 0 && x < 12 && x % 2 == 0);
}

pub fn joinable_post_v2(x: u64) -> u64 {
    let y = x;
    assumed_postcondition!(y > 0);
    assumed_postcondition!(y < 10);
    assumed_postcondition!(y % 2 == 0);
    return y;
}

pub fn test_joinable_post_v2(x: u64) {
    let y = joinable_post_v2(x);
    verify!(y > 0 && y < 12 && y % 2 == 0);
}

pub fn main() {}
