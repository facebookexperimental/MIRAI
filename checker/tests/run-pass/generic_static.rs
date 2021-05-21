// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Checks that trait implementations with constant overrides are handled correctly.

use mirai_annotations::*;

pub trait T {
    const FOO: bool = false;
}

pub struct A {}

impl T for A {
    const FOO: bool = true;
}

pub fn p<X: T>() {
    precondition!(X::FOO)
}

pub fn t1() {
    p::<A>();
}

pub fn main() {}
