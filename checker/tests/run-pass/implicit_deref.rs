// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test that checks if implicit/explicit dereference works properly when doing weak updates

use mirai_annotations::*;

struct I32 {
    content: i32,
}

pub fn implicit_deref(cond: bool) {
    let mut left = I32 { content: 1234 };
    let mut right = I32 { content: 4321 };
    let join: &mut I32;
    if cond {
        join = &mut left;
    } else {
        join = &mut right;
    }
    join.content = 3333; // implicit deref
    verify!(left.content == 3333 || right.content == 3333);
}

pub fn explicit_deref(cond: bool) {
    let mut left = 1234;
    let mut right = 4321;
    let join: &mut i32;
    if cond {
        join = &mut left;
    } else {
        join = &mut right;
    }
    *join = 3333; // explicit deref
    verify!(left == 3333 || right == 3333);
}

pub fn main() {}
