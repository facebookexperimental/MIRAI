// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that takes the address of a local copy of a parameter of type struct

use mirai_annotations::*;

#[derive(Clone, Copy)]
struct Foo {
    bar: i32,
}

fn foo(f: Foo) -> i32 {
    let g: Foo = f;
    foo2(&g)
}

fn foo2(f: &Foo) -> i32 {
    f.bar
}

pub fn test1() {
    let f = Foo { bar: 1 };
    let i = foo(f);
    verify!(i == 1);
}

pub fn main() {}
