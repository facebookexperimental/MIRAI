// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that calls std::intrinsics::unreachable unconditionally.

#![allow(internal_features)]
#![feature(core_intrinsics)]
#![allow(unused)]

use mirai_annotations::*;

use std::intrinsics;

pub fn foo() {
    unsafe {
        intrinsics::unreachable();
    }
    panic!("whoa, shouldn't get here");
}

pub fn foo2() -> i32 {
    assume_unreachable!();
    panic!("whoa, shouldn't get here");
}

pub fn foo3() {
    verify_unreachable!(); //~ statement is reachable
    panic!("whoa, shouldn't get here");
}

pub fn foo4() -> i32 {
    panic!("shouldn't get past here"); //~ shouldn't get past here
    verify_unreachable!();
}

pub fn foo5(x: Option<i32>) -> i32 {
    x.unwrap_or_else(|| foo2())
}

fn panic_a_bit() -> i32 {
    panic!("aaargh!"); //~ related location
}

pub fn foo6(x: Option<i32>) -> i32 {
    x.unwrap_or_else(|| panic_a_bit()) //~ possible aaargh!
}
//~ related location

pub fn main() {}
