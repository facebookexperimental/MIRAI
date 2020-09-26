// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a static array.

use mirai_annotations::*;

static POWERS_10: [u32; 10] = [
    1,
    10,
    100,
    1_000,
    10_000,
    100_000,
    1_000_000,
    10_000_000,
    100_000_000,
    1_000_000_000,
];

fn get_power(i: usize) -> u32 {
    POWERS_10[i]
}

pub fn main() {
    let x = get_power(2);
    verify!(x == 100);
}
