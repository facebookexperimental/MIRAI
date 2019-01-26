// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that exercises the numeric parts of visit_constant.

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
pub static O:f32 = 15.6;
pub static P:f64 = 15.6666666666666666666666;

pub fn main() {
    debug_assert!(A == -1);
    debug_assert!(B == 2);
    debug_assert!(C == -3);
    debug_assert!(D == 4);
    debug_assert!(E == -5);
    debug_assert!(F == 6);
    debug_assert!(G == -7);
    debug_assert!(H == 8);
    debug_assert!(I == -9);
    debug_assert!(J == 10);
    debug_assert!(K == -11);
    debug_assert!(L == 12);
    debug_assert!(M == -13);
    debug_assert!(N == 14);
    debug_assert!(O == 15.6);
    debug_assert!(P == 15.6666666666666666666666);
}
