// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks for widening in recursive loops

use mirai_annotations::*;

fn fib(x: u64) -> u64 {
    match x {
        0 => 0,
        1 => 1,
        _ => fib(x - 1) + fib(x - 2), //~ possible attempt to add with overflow
    }
}

pub fn main() {
    let x = fib(6);
    verify!(x == 8); //~ possible false verification condition
}
