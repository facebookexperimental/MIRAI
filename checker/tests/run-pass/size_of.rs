// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that size_of::<T>() is handled correctly for a struct

use mirai_annotations::*;
use std::mem::size_of;

pub struct Foo {
    pub bar: i32,
    pub baz: f64,
}

pub fn main() {
    verify!(size_of::<Foo>() == 16);
}
