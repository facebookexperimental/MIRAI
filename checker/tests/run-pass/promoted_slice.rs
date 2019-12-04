// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses MIR constant array slice literals.

//todo: since the only way I can find to generate such literals is by using them in
// tags of match expressions, and these call to std::cmp::PartialEq::eq, there is currently
// no way to check that these constants are read correctly, other than by logging.
// Once we have a really precise summary for std::cmp::PartialEq::eq, we should be able
// to prove things, for example we should be able to assert that promote_u8 returns 10
// if called with &[1, 2, 3].

pub fn promote_u8(value: &[u8]) -> u8 {
    const TAG: &[u8] = &[1, 2, 3];
    match value {
        TAG => 10,
        _ => 20,
    }
}

pub fn promote_u16(value: &[u16]) -> u16 {
    const TAG: &[u16] = &[1, 2, 3];
    match value {
        TAG => 10,
        _ => 20,
    }
}

pub fn promote_u32(value: &[u32]) -> u32 {
    const TAG: &[u32] = &[1, 2, 3];
    match value {
        TAG => 10,
        _ => 20,
    }
}

pub fn promote_u64(value: &[u64]) -> u64 {
    const TAG: &[u64] = &[1, 2, 3];
    match value {
        TAG => 10,
        _ => 20,
    }
}

pub fn promote_u128(value: &[u128]) -> u128 {
    const TAG: &[u128] = &[1, 2, 3];
    match value {
        TAG => 10,
        _ => 20,
    }
}

pub fn promote_usize(value: &[usize]) -> usize {
    const TAG: &[usize] = &[1, 2, 3];
    match value {
        TAG => 10,
        _ => 20,
    }
}

pub fn promote_i8(value: &[i8]) -> i8 {
    const TAG: &[i8] = &[1, 2, -3];
    match value {
        TAG => 10,
        _ => 20,
    }
}

pub fn promote_i16(value: &[i16]) -> i16 {
    const TAG: &[i16] = &[1, 2, -3];
    match value {
        TAG => 10,
        _ => 20,
    }
}

pub fn promote_i32(value: &[i32]) -> i32 {
    const TAG: &[i32] = &[1, 2, -3];
    match value {
        TAG => 10,
        _ => 20,
    }
}

pub fn promote_i64(value: &[i64]) -> i64 {
    const TAG: &[i64] = &[1, 2, -3];
    match value {
        TAG => 10,
        _ => 20,
    }
}

pub fn promote_i128(value: &[i128]) -> i128 {
    const TAG: &[i128] = &[1, 2, -3];
    match value {
        TAG => 10,
        _ => 20,
    }
}

pub fn promote_isize(value: &[isize]) -> isize {
    const TAG: &[isize] = &[1, 2, -3];
    match value {
        TAG => 10,
        _ => 20,
    }
}

pub fn main() {}
