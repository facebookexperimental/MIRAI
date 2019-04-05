// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that declares a precondition and report a failure to satisfy it.

#[macro_use]
extern crate mirai_annotations;

pub fn main() {
    let mut a = [1, 2];
    foo(&mut a, 3); //~ unsatisfied precondition
}

fn foo(arr: &mut [i32; 2], i: usize) {
    precondition!(i < 2); //~ related location
    arr[i] = 12;
}

pub fn bad_foo(arr: &mut [i32; 2], i: usize) {
    if i > 0 {
        precondition!(i < 2); //~ preconditions should be reached unconditionally
    }
    arr[i] = 12; //~ possible array index out of bounds
}
