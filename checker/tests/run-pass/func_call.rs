// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a function summary.

use mirai_annotations::*;

struct Foo {
    x: i32,
}

fn foo() -> i32 {
    123
}
fn bar(x: f32) -> f32 {
    x + 1.0
}
fn bas(foo: &mut Foo) {
    foo.x = 456;
}
pub fn main() {
    verify!(foo() == 123);
    verify!(bar(1.0) == 2.0);
    let mut f = Foo { x: 123 };
    bas(&mut f);
    verify!(f.x == 456);
}
