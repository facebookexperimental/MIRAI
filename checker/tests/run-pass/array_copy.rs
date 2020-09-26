// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that fixed size arrays passed as parameters are copied when de-referenced

use mirai_annotations::*;

fn f(arr: &mut [i32; 3]) {
    arr[2] = 345;
}

pub fn g(_x: i32, arr: &mut [i32; 3]) {
    let mut a = *arr;
    f(&mut a);
}

pub fn main() {
    let mut arr = [1, 2, 3];
    g(0, &mut arr);
    verify!(arr[2] == 3);
}
