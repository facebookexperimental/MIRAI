// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that std::intrinsics::discriminant_value is properly implemented.

#![allow(internal_features)]
#![feature(core_intrinsics)]

use mirai_annotations::*;
use std::mem;

pub enum Foo {
    A(&'static str),
    B(i32),
    C(i32),
}

pub fn main() {
    let x = std::intrinsics::discriminant_value(&Foo::B(1));
    let y = std::intrinsics::discriminant_value(&Foo::B(2));
    verify!(x == y);
    verify!(mem::discriminant(&Foo::A("bar")) == mem::discriminant(&Foo::A("baz")));
    verify!(mem::discriminant(&Foo::B(1)).eq(&mem::discriminant(&Foo::B(2))));
    verify!(mem::discriminant(&Foo::B(3)) != mem::discriminant(&Foo::C(3)));
    let i = 1;
    verify!(std::intrinsics::discriminant_value(&i) == 0);
}
