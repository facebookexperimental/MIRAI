// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a closure call result that includes a closed over variable value.

use mirai_annotations::*;

fn foo<F>(f: F) -> i32
where
    F: FnOnce() -> i32,
{
    f()
}

pub fn main() {
    let x = 1;
    let f = || x;
    let y = foo(f);
    verify!(y == 1);
}
