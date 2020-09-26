// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that declares a precondition and report a failure to satisfy it.

use mirai_annotations::*;

pub fn main() {
    let mut a = [1, 2];
    foo(&mut a, 3); //~ unsatisfied precondition: i should be 0 or 1
}

fn foo(arr: &mut [i32; 2], i: usize) {
    precondition!(i < 2, "i should be 0 or 1"); //~ related location
    arr[i] = 12;
}

pub fn bad_foo(arr: &mut [i32; 2], i: usize) {
    //todo: fix this
    if i > 0 {
        precondition!(i < 2); // ~ preconditions should be reached unconditionally
    }
    arr[i] = 12;
}

pub fn good_foo(a: &[i32; 2], i: usize) {
    precondition!({
        let j = if i == 0 { 1 } else { 0 };
        a[j] > 50
    });
}
