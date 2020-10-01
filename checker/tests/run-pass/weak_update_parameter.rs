// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that assigns to an unknown index of a mutable array parameter

use mirai_annotations::*;

fn test(a: &mut [i32; 4], i: usize) {
    a[i] = 666;
}

pub fn main() {
    let mut v = [1, 2, 3, 4];
    let i = abstract_value!(1);
    assume!(i < 4);
    test(&mut v, i);
    verify!(v[1] == 2 || v[1] == 666);
    verify!(v[1] == 666); //~ possible false verification condition
}
