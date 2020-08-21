// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that calls a closure returned from a function.

use mirai_annotations::*;

fn bar() -> impl FnOnce(i32) -> i32 {
    let x = 1;
    move |i| i + x
}

pub fn main() {
    let b = bar();
    let y = b(0);
    verify!(y == 1);
}
