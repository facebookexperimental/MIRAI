// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses assert! to declares a precondition and report a failure to satisfy it.

pub fn main() {
    let mut a = [1, 2];
    foo(&mut a, 3); //~ possible error: assertion failed: i < 2
}

fn foo(arr: &mut [i32; 2], i: usize) {
    assert!(i < 2); //~ related location
    arr[i] = 12;
}
