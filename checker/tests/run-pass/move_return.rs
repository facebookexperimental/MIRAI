// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that non primitive values can move through a generic copy.

use mirai_annotations::*;

fn id<T>(x: T) -> T {
    x
}

struct Foo {
    x: i32,
    y: i32,
}

pub fn main() {
    let foo = Foo { x: 1, y: 2 };
    verify!(foo.x == 1);
    let foo2 = id(foo);
    verify!(foo2.y == 2);
}
