// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that exercises the numeric parts of visit_constant.

use mirai_annotations::*;

pub static A: isize = -1;
pub static B: usize = 2;
pub static C: i8 = -3;
pub static D: u8 = 4;
pub static E: i16 = -5;
pub static F: u16 = 6;
pub static G: i32 = -7;
pub static H: u32 = 8;
pub static I: i32 = -9;
pub static J: u32 = 10;
pub static K: i64 = -11;
pub static L: u64 = 12;
pub static M: i128 = -13;
pub static N: u128 = 14;
pub static O: f32 = 15.6;
pub static P: f64 = 15.6666666666666666666666;

pub fn main() {
    verify!(A == -1);
    verify!(B == 2);
    verify!(C == -3);
    verify!(D == 4);
    verify!(E == -5);
    verify!(F == 6);
    verify!(G == -7);
    verify!(H == 8);
    verify!(I == -9);
    verify!(J == 10);
    verify!(K == -11);
    verify!(L == 12);
    verify!(M == -13);
    verify!(N == 14);
    verify!(O == 15.6);
    verify!(P == 15.6666666666666666666666);
}
