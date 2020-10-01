// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses checked_add

use mirai_annotations::*;

pub struct Foo {
    capacity: usize,
    length: usize,
}

impl Foo {
    pub fn len(&self) -> usize {
        self.double().1
    }

    pub fn grow(&mut self, new_cap: usize) {
        precondition!(self.len() <= new_cap);
        self.capacity = new_cap;
    }

    pub fn reserve_exact(&mut self, additional: usize) {
        let (&mut len, cap) = self.double_mut();
        let new_cap = if cap - len < additional {
            match len.checked_add(additional) {
                Some(cap) => {
                    self.grow(cap);
                    cap
                }
                None => assume_unreachable!("can't get here"),
            }
        } else {
            cap
        };
        assumed_postcondition!(new_cap >= cap);
    }

    fn double(&self) -> (usize, usize) {
        let result = (self.length, self.capacity);
        assumed_postcondition!(result.0 <= result.1);
        result
    }

    fn double_mut(&mut self) -> (&mut usize, usize) {
        let result = (&mut self.length, self.capacity);
        assumed_postcondition!(*result.0 <= result.1);
        result
    }
}

pub fn main() {}
