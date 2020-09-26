// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Tests constant folding of arithmetic binary operations

use mirai_annotations::*;

pub fn main() {
    tu8();
    ti8();
    tf32();
    tf64();
}

fn tu8() {
    let mut a: u8 = 255;
    a &= 254;
    verify!(a == 254);
    a |= 1;
    verify!(a == 255);
    a -= 1;
    verify!(a == 254);
    a += 1;
    verify!(a == 255);
    a ^= 254;
    verify!(a == 1);
    a *= 2;
    verify!(a == 2);
    a /= 2;
    verify!(a == 1);
    a %= 1;
    verify!(a == 0);
    a += 1;
    verify!(a == 1);
    a <<= 2;
    verify!(a == 4);
    a >>= 1;
    verify!(a == 2);
    a -= 1;
    verify!(a == 1);
}

fn ti8() {
    let mut a: i8 = 126;
    a &= 127;
    verify!(a == 126);
    a |= 1;
    verify!(a == 127);
    a ^= 126;
    verify!(a == 1);
    a *= -10;
    verify!(a == -10);
    a /= 2;
    verify!(a == -5);
    a %= 10;
    verify!(a == -5);
    a += 1;
    verify!(a == -4);
    a <<= 2;
    verify!(a == -16);
    a >>= 3;
    verify!(a == -2);
    a -= 1;
    verify!(a == -3);
}

fn tf32() {
    let mut a: f32 = 123.456786;
    a += 1.1;
    verify!(a == 124.556786);
    a *= 100.0;
    verify!(a == 12455.6786);
    a /= 10.0;
    verify!(a == 1245.56786);
    a %= 10.0;
    verify!(a == 5.567871);
    a -= 1.0;
    verify!(a == 4.567871);
}

fn tf64() {
    let mut a: f64 = 123.45678901233999;
    a += 1.1;
    verify!(a == 124.55678901233999);
    a *= 100.0;
    verify!(a == 12455.678901234);
    a /= 10.0;
    verify!(a == 1245.5678901234);
    a %= 10.0;
    verify!(a == 5.567890123400048);
    a -= 1.0;
    verify!(a == 4.567890123400048);
}
