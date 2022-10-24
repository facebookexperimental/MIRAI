// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// This tests the devirtualization needed for the contracts crate to work for MIRAI.

// MIRAI_FLAGS --test_only

use mirai_annotations::*;

// Without using contracts crate directly, this is what #[contract_trait] will generate.
trait Adder {
    // Get the state of the adder for use in contracts. This is a common design pattern to
    // access state of trait implementations on abstract trait level.
    fn current(&self) -> i32;

    // Original function decrement with pre/post embedded calling a newly introduced impl function.
    // That's conceptually what the contract crate generates for pre/post on trait methods.
    fn decrement(&mut self) {
        checked_precondition!(self.current() > 0);
        let old = self.current();
        self._impl_decrement();
        checked_postcondition!(self.current() < old);
    }

    fn _impl_decrement(&mut self);
}

struct MyAdder(i32);

impl Adder for MyAdder {
    fn current(&self) -> i32 {
        self.0
    }

    fn _impl_decrement(&mut self) {
        self.0 = self.0 - 1;
    }
}

#[test]
pub fn test() {
    let mut a = MyAdder(3);
    a.decrement();
    checked_verify!(a.current() < 3);
    // todo: fix this
    verify!(a.current() == 1); // ~ provably false verification condition
}

pub fn main() {}
