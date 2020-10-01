// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that promotes a local from a callee to a caller

use mirai_annotations::*;

pub struct Foo {
    pub x: i64,
    pub y: i64,
}

pub struct Bar {
    pub foo1: Foo,
    pub foo2: Foo,
}

pub fn callee(arg: &mut Bar) {
    arg.foo1 = make_foo();
    arg.foo2 = make_foo();
}

pub fn caller() {
    let mut bar = Bar {
        foo1: Foo { x: 1, y: 2 },
        foo2: Foo { x: 3, y: 4 },
    };
    callee(&mut bar);
    callee(&mut bar);
}

pub fn make_foo() -> Foo {
    result!()
}

pub fn main() {}
