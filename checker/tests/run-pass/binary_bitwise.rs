// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Tests constant folding of bitwise binary operations

use mirai_annotations::*;

pub fn main() {
    tu1();
    tu8();
    ti8();
}

fn tu1() {
    let mut b = true;
    b &= true;
    verify!(b);
    b &= false;
    verify!(!b);
    b |= false;
    verify!(!b);
    b |= true;
    verify!(b);
    b &= false;
    verify!(!b);
    b &= true;
    verify!(!b);
    b = true | b;
    verify!(b);
    b ^= true;
    verify!(!b);
    b ^= false;
    verify!(!b);
    b ^= true;
    verify!(b);
    b ^= false;
    verify!(b);
}

fn tu8() {
    let mut a: u8 = 0x11;
    a &= 0x10;
    verify!(a == 0x10);
    a |= 1;
    verify!(a == 0x11);
    a ^= 0x10;
    verify!(a == 0x01);
}

fn ti8() {
    let mut a: i8 = 0x11;
    a &= 0x10;
    verify!(a == 0x10);
    a |= 1;
    verify!(a == 0x11);
    a ^= 0x10;
    verify!(a == 0x01);
}
