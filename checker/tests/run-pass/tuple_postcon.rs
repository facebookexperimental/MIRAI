// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that assumes a post condition on a structured return value

use mirai_annotations::assumed_postcondition;

pub struct Foo {
    capacity: usize,
    length: usize,
}

impl Foo {
    pub fn reserve(&mut self) {
        let (&mut len, cap) = self.double_mut();
        let _ = cap - len;
    }

    fn double_mut(&mut self) -> (&mut usize, usize) {
        let result = (&mut self.length, self.capacity);
        assumed_postcondition!(*result.0 <= result.1);
        result
    }
}

pub fn main() {}
