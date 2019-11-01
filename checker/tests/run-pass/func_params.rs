// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a function parameter

#[macro_use]
extern crate mirai_annotations;

fn bar(x: Option<i32>, j: i32) -> Option<i32> {
    match x {
        Some(i) => Some(i << 1),
        None => Some(j),
    }
}

fn bas(x: Option<i32>, j: i32) -> Option<i32> {
    match x {
        Some(i) => Some(i << 2),
        None => Some(j),
    }
}

fn foo(f: fn(Option<i32>, i32) -> Option<i32>) -> Option<i32> {
    f(Some(1), 1)
}

pub fn main() {
    let fbar = foo(bar);
    verify!(fbar.unwrap() == 2);
    let fbas = foo(bas);
    verify!(fbas.unwrap() == 4);
}
