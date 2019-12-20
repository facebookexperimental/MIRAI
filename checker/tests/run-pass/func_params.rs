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

fn bas<T>(x: Option<T>, j: T) -> Option<T> {
    match x {
        Some(i) => Some(i),
        None => Some(j),
    }
}

fn foo(f: fn(Option<i32>, i32) -> Option<i32>) -> Option<i32> {
    f(Some(1), 1)
}

fn foos<T: Copy>(f: fn(Option<T>, T) -> Option<T>, x: T) -> Option<T> {
    f(Some(x), x)
}

pub fn main() {
    let fbar = foo(bar);
    verify!(fbar.unwrap() == 2);
    let fbas = foos(bas, 2);
    verify!(fbas.unwrap() == 2);
}
