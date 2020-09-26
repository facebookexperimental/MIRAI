// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that non primitive values can move through a generic copy.

use mirai_annotations::*;

fn mutate_and_then_copy(dest: &mut (i32, i32), src: &mut (i32, i32)) {
    src.1 = 789;
    *dest = *src;
}

pub fn main() {
    let mut a = (123, 456);
    let mut b = (456, 123);
    mutate_and_then_copy(&mut a, &mut b);
    verify!(b.0 == 456 && b.1 == 789);
    verify!(a.0 == 456 && a.1 == 789);
}
