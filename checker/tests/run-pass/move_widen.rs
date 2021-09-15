// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that copies widened values

use mirai_annotations::*;

pub fn t1(n: u32) {
    let mut i: u32 = 0;
    let mut j: u32 = 0;
    while i < n {
        //todo: fix this
        verify!(i == j); //~ possible false verification condition
        i += 1;
        j = i;
    }
}

pub fn main() {}
