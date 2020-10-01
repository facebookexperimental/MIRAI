// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses built-in contracts for the Vec struct.

use mirai_annotations::*;

struct Test {
    v: Vec<u8>,
}

impl Test {
    fn new() -> Self {
        let res = Self { v: vec![] };
        assumed_postcondition!(res.v.is_empty());
        res
    }
}

pub fn main() {
    let t = Test::new();
    verify!(t.v.is_empty());
}
