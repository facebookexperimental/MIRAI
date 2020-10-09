// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a function summary where the return value is a structure.

use mirai_annotations::*;

struct Foo {
    x: i32,
}
fn foo() -> Foo {
    Foo { x: 123 }
}
pub fn main() {
    let f = foo();
    let fx = f.x;
    verify!(fx == 123);
}
