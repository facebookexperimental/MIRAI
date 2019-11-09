// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses an explicit post condition.

#[macro_use]
extern crate mirai_annotations;

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

pub fn bar(c: bool) -> u64 {
    let result = result!();
    if c {
        assumed_postcondition!(result < 5);
    } else {
        assumed_postcondition!(result > 10);
    }
    result
}

pub fn main() {}
