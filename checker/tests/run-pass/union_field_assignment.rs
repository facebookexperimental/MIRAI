// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that assignments to one field of a union result in updates of all
// the union fields, transmuting as necessary.

use mirai_annotations::*;

#[allow(non_camel_case_types)]
#[derive(Copy, Clone, PartialEq)]
pub struct __m128i(i64, i64);

#[allow(non_camel_case_types)]
#[derive(Copy, Clone)]
#[allow(dead_code)]
pub union vec128_storage {
    u32x4: [u32; 4],
    u64x2: [u64; 2],
    u128x1: [u128; 1],
    sse2: __m128i,
}

fn get_union1(u32x4: [u32; 4]) -> vec128_storage {
    vec128_storage { u32x4 }
}

pub fn t1() {
    let u64x2 = [1, 0, 2, 0];
    let u = get_union1(u64x2);
    unsafe {
        verify!(u.u32x4[0] == 1);
        verify!(u.u32x4[1] == 0);
        verify!(u.u32x4[2] == 2);
        verify!(u.u32x4[3] == 0);
        verify!(u.u64x2[0] == 1);
        verify!(u.u64x2[1] == 2);
        verify!(u.u128x1[0] == (2u128 << 64) + 1);
        verify!(u.sse2 == __m128i(1, 2));
    }
}

fn get_union2(u64x2: [u64; 2]) -> vec128_storage {
    vec128_storage { u64x2 }
}

pub fn t2() {
    let u64x2 = [1, 2];
    let u = get_union2(u64x2);
    unsafe {
        verify!(u.u32x4[0] == 1);
        verify!(u.u32x4[1] == 0);
        verify!(u.u32x4[2] == 2);
        verify!(u.u32x4[3] == 0);
        verify!(u.u64x2[0] == 1);
        verify!(u.u64x2[1] == 2);
        verify!(u.u128x1[0] == (2u128 << 64) + 1);
        verify!(u.sse2 == __m128i(1, 2));
    }
}

fn get_union3(u128x1: [u128; 1]) -> vec128_storage {
    vec128_storage { u128x1 }
}

pub fn t3() {
    let u128x1 = [(2u128 << 64) + 1];
    let u = get_union3(u128x1);
    unsafe {
        verify!(u.u32x4[0] == 1);
        verify!(u.u32x4[1] == 0);
        verify!(u.u32x4[2] == 2);
        verify!(u.u32x4[3] == 0);
        verify!(u.u64x2[0] == 1);
        verify!(u.u64x2[1] == 2);
        verify!(u.u128x1[0] == (2u128 << 64) + 1);
        verify!(u.sse2 == __m128i(1, 2));
    }
}

fn get_union4(sse2: __m128i) -> vec128_storage {
    vec128_storage { sse2 }
}

pub fn t4() {
    let sse2 = __m128i(1, 2);
    let u = get_union4(sse2);
    unsafe {
        verify!(u.u32x4[0] == 1);
        verify!(u.u32x4[1] == 0);
        verify!(u.u32x4[2] == 2);
        verify!(u.u32x4[3] == 0);
        verify!(u.u64x2[0] == 1);
        verify!(u.u64x2[1] == 2);
        verify!(u.u128x1[0] == (2u128 << 64) + 1);
        verify!(u.sse2 == sse2);
    }
}

pub union U1 {
    x: u32,
    y: [u8; 4],
}

pub fn t5() {
    let u = U1 { x: 257 };
    unsafe {
        verify!(u.x == 257);
        verify!(u.y[0] == 1);
        verify!(u.y[1] == 1);
        verify!(u.y[2] == 0);
        verify!(u.y[3] == 0);
    }
}

pub fn t6() {
    let u = U1 { y: [1, 1, 0, 0] };
    unsafe {
        verify!(u.x == 257);
        verify!(u.y[0] == 1);
        verify!(u.y[1] == 1);
        verify!(u.y[2] == 0);
        verify!(u.y[3] == 0);
    }
}

pub union U2 {
    pub x: u64,
    pub y: [u8; 4],
}

pub fn t7() {
    let _u = U2 { y: [1, 1, 0, 0] }; //~ The union is not fully initialized by this assignment
}

pub union U3 {
    pub x: (u32, u32),
    pub y: u32,
}

pub fn t8() {
    let _u = U3 { y: 1 }; //~ The union is not fully initialized by this assignment
}
pub fn main() {}
