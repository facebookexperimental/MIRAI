// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// Bug regression

pub fn foo(v: Vec<i32>) {
    let _ = v.as_slice().split_first();
}

pub fn main() {}
