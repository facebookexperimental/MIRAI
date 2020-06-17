// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that assigns to a location of type struct that is unknown at compile time.

#[macro_use]
extern crate mirai_annotations;

struct Bool {
    content: bool,
}

pub fn test(cond: bool) {
    let mut left = Bool { content: false };
    let mut right = Bool { content: false };
    let join;
    if cond {
        join = &mut left;
    } else {
        join = &mut right;
    }
    *join = Bool { content: true };
    verify!(left.content || right.content);
}

pub fn main() {}
