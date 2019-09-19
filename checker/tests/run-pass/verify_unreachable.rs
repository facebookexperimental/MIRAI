// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses built-in contracts for the Vec struct.

#![allow(unused)]

#[macro_use]
extern crate mirai_annotations;

fn foo1(i: i32) {
    if i < 10 {
        assume_unreachable!();
    }
}

fn foo2(i: i32) {
    if i < 10 {
        verify_unreachable!(); //~ statement is reachable
    }
}

pub fn main() {}
