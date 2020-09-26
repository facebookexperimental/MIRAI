// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a function summary where there is a side effect on a mutable reference.

use mirai_annotations::*;

struct Foo {
    x: i32,
}
fn foo(f: &mut Foo) {
    f.x = 456;
}
pub fn main() {
    let mut f = Foo { x: 123 };
    foo(&mut f);
    let fx = f.x;
    verify!(fx == 456);
}
