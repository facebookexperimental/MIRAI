// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test for VecDeque::push_front

use mirai_annotations::*;

use std::collections::VecDeque;

pub fn main() {
    let mut v: VecDeque<i32> = VecDeque::new();
    let old_len = v.len();
    verify!(old_len == 0);
    v.push_front(0);
    verify!(v.len() == old_len + 1);
}
