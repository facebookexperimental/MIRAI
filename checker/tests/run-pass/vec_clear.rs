// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// This tests the Vector clear method

use mirai_annotations::*;

pub fn main() {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.clear();
    verify!(v.is_empty());
}
