// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that infers a precondition and report a failure to satisfy it.

fn foo(arr: &mut [i32], i: usize) {
    arr[i] = 12; //~ related location
}

pub fn main() {
    let mut a = [1, 2];
    foo(&mut a, 3); //~ array index out of bounds
}
