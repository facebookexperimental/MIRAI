// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that pre-state can be used after modification.

use mirai_annotations::*;

pub struct Foo {
    pub bar: *const i32,
}

impl Foo {
    pub fn t1(&mut self) {
        let s1 = self.bar;
        self.bar = 1 as *const i32;
        verify!(s1 == self.bar); //~ possible false verification condition
    }
}

pub fn main() {}
