// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that needs to do cleanup if an array access is out of bounds.

pub fn foo(arr: &mut [i32], i: usize) -> String {
    arr[i] = 123; //~ possible array index out of bounds
    let result = String::from("foo");
    let _e = arr[i]; // no warning here because we can't get here unless line 10 succeeded
    result
}
