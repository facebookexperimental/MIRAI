// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that assumes a post condition on a structured return value

use mirai_annotations::*;

pub struct Foo {
    capacity: usize,
    length: usize,
}

impl Foo {
    pub fn reserve(&mut self, additional: usize) {
        let (&mut len, cap) = self.double_mut();
        let new_cap = if cap - len < additional {
            len.checked_add(additional)
                .and_then(usize::checked_next_power_of_two)
                .unwrap_or(usize::max_value())
        } else {
            cap
        };
        assumed_postcondition!(new_cap >= cap);
    }

    fn double_mut(&mut self) -> (&mut usize, usize) {
        let result = (&mut self.length, self.capacity);
        assumed_postcondition!(*result.0 <= result.1);
        result
    }
}

pub fn main() {}
