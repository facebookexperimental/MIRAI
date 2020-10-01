// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that closure fields are tracked accurately.

use mirai_annotations::*;

pub fn main() {
    let x = 1;
    let f = || x << 1;
    let g = f();
    verify!(g == 2);

    let mut mx = 4;
    let mut mf = |i, j| {
        mx = i;
        j
    };
    let mr = mf(1, 2);
    verify!(mx == 1);
    verify!(mr == 2);
    verify!(x == 2); //~ provably false verification condition
}
