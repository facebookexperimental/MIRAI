// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Tests for std::mem::replace

use mirai_annotations::*;

use std::mem;

pub fn t1() {
    let mut a = [1, 2];
    let b = [3, 4];

    let old_a = mem::replace(&mut a, b);
    verify!(old_a[0] == 1);
    verify!(old_a[1] == 2);
    verify!(a[0] == 3);
    verify!(a[1] == 4);
}

pub fn main() {}
