// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that indexes into a parameter of type fixed size array

pub fn foo(a: [i32; 10], i: usize) -> i32 {
    if i < a.len() {
        a[i]
    } else {
        -99999
    }
}

pub fn main() {}
