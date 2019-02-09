// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Tests constant folding of arithmetic binary operations

pub fn main() {
    ti();
    tf();
}

fn ti() {
    let mut a: i8 = 127;
    a = -a;
    debug_assert!(a == -127);
    a -= 1;
    debug_assert!(a == -128);
    let _a = -a; //~ attempt to negate with overflow
}

fn tf() {
    let mut a: f32 =   123.456786;
    a = -a;
    debug_assert!(a == -123.456786);
    let mut b: f64 =   123.45678901233999;
    b = -b;
    debug_assert!(b == -123.45678901233999);
}
