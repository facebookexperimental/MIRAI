// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// This tests the Vector append method

#[macro_use]
extern crate mirai_annotations;

pub fn main() {
    let mut v1: Vec<i32> = Vec::new();
    let mut v2: Vec<i32> = Vec::new();
    v2.push(1);
    v1.append(&mut v2);
    verify!(v1.len() == 1); //~ possible false verification condition
}
