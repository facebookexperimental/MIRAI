// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that a function can return a copy of its parameter.

use mirai_annotations::*;

pub fn foo<P>(f: &P) -> P
where
    P: Copy,
{
    *f
}

pub fn main() {
    let y = 1;
    let x = foo(&y);
    verify!(x == y);
}
