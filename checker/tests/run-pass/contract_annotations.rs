// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Tests for annotations from the contracts crate.

// MIRAI_FLAGS --test_only

use contracts::*;
use mirai_annotations::*;

pub fn main() {
    use_pre_post();
    use_trait();
    use_invariant();
}

// Simple pre/post
// ---------------

#[requires(x > 0)]
#[ensures(ret >= x)]
fn pre_post(x: i32) -> i32 {
    return x;
}

#[test]
fn use_pre_post() {
    checked_verify!(pre_post(1) >= 1);
}

// Trait pre/post

#[contract_trait]
trait Adder {
    fn get(&self) -> i32;

    #[requires(x > 0)]
    #[requires(self.get() <= std::i32::MAX - x)]
    #[ensures(ret == old(self.get()) && self.get() > old(self.get()))]
    fn get_and_add(&mut self, x: i32) -> i32;
}

struct MyAdder {
    x: i32,
}

#[contract_trait]
impl Adder for MyAdder {
    fn get(&self) -> i32 {
        self.x
    }
    fn get_and_add(&mut self, x: i32) -> i32 {
        let c = self.x;
        self.x = self.x + x;
        return c;
    }
}

#[test]
fn use_trait() {
    let mut a = MyAdder { x: 1 };
    checked_verify!(a.get() == 1);
    checked_verify!(a.get_and_add(2) == 1);
    checked_verify!(a.get() == 3);
}

// Invariants
// ==========

struct S {
    x: i32,
}

#[debug_invariant(self.x > 0)]
impl S {
    #[requires(self.x < std::i32::MAX)]
    #[ensures(ret == old(self.x))]
    fn get_and_decrement(&mut self) -> i32 {
        let c = self.x;
        self.x = self.x + 1;
        return c;
    }
}

#[test]
fn use_invariant() {
    let mut s = S { x: 1 };
    checked_verify!(s.get_and_decrement() == 1);
}
