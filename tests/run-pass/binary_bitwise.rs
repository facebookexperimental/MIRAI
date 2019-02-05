// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Tests constant folding of bitwise binary operations

pub fn main() {
    tu1();
    tu8();
    ti8();
}

fn tu1() {
    let mut b = true;
    b &= true;
    debug_assert!(b);
    b &= false;
    debug_assert!(!b);
    b |= false;
    debug_assert!(!b);
    b |= true;
    debug_assert!(b);
    b &= false;
    debug_assert!(!b);
    b &= true;
    debug_assert!(!b);
    b = true | b;
    debug_assert!(b);
    b ^= true;
    debug_assert!(!b);
    b ^= false;
    debug_assert!(!b);
    b ^= true;
    debug_assert!(b);
    b ^= false;
    debug_assert!(b);
}

fn tu8() {
    let mut a: u8 = 0x11;
    a &= 0x10;
    debug_assert!(a == 0x10);
    a |= 1;
    debug_assert!(a == 0x11);
    a ^= 0x10;
    debug_assert!(a == 0x01);
}

fn ti8() {
    let mut a: i8 = 0x11;
    a &= 0x10;
    debug_assert!(a == 0x10);
    a |= 1;
    debug_assert!(a == 0x11);
    a ^= 0x10;
    debug_assert!(a == 0x01);
}