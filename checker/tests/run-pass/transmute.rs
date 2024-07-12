// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses std::mem::transmute

#![allow(internal_features)]
#![feature(core_intrinsics)]

use mirai_annotations::*;

pub unsafe fn t1(ptr: *mut i32) {
    *ptr = 123;
    let non_null_ptr = std::ptr::NonNull::new_unchecked(ptr);
    let ptr2 = std::mem::transmute::<std::ptr::NonNull<i32>, *const i32>(non_null_ptr);
    verify!(*ptr2 == 123);
}

pub unsafe fn t2(ptr: *mut i32) {
    *ptr = 123;
    let non_null_ptr = std::mem::transmute::<*const i32, std::ptr::NonNull<i32>>(ptr);
    verify!(*non_null_ptr.as_ptr() == 123);
}

pub unsafe fn t3() {
    let a = std::alloc::alloc(std::alloc::Layout::from_size_align(4, 2).unwrap());
    let cptr = std::intrinsics::arith_offset(a, 2);
    let bptr: *mut u8 = std::mem::transmute::<*const u8, *mut u8>(cptr);
    *bptr = 7;
    verify!(*cptr == 7);
    let cptr1 = std::intrinsics::arith_offset(cptr, 1);
    let bptr1: *mut u8 = std::mem::transmute::<*const u8, *mut u8>(cptr1);
    *bptr1 = 1;
    verify!(*cptr1 == 1);
    // todo: smash together byte pairs in the heap model when this kind of cast happens
    // let ptr0 = std::mem::transmute::<*mut u8, *mut u16>(a);
    // let ptr1 = std::intrinsics::arith_offset(ptr0, 1);
    // println!("{}", *ptr1);
}

#[derive(Clone, Copy)]
pub struct A {
    pub x: i16,
    pub y: i16,
}

struct B {
    x0: i8,
    x1: i8,
    y0: i8,
    y1: i8,
}

#[repr(packed)]
struct BIB {
    b1: bool,
    i: i16,
    b2: bool,
}

struct BA {
    a: BIB,
}

struct CH {
    c: char,
}

struct F {
    f: f32,
}

pub unsafe fn t4() {
    let a = A { x: -1, y: -256 };
    let b = std::mem::transmute::<A, B>(a);
    verify!(b.x0 == -1);
    verify!(b.x1 == -1);
    verify!(b.y0 == 0);
    verify!(b.y1 == -1);
    let a = A { x: -1, y: -256 };
    let f = std::mem::transmute::<A, F>(a);
    verify!(f.f == -171470400000000000000000000000000000000.0);
    let a = A { x: -1, y: -256 };
    let ba = std::mem::transmute::<A, BA>(a);
    verify!(ba.a.b1 == true);
    verify!(ba.a.i == 255);
    verify!(ba.a.b2 == true);
    let a = A { x: -1, y: 4 };
    let ch = std::mem::transmute::<A, CH>(a);
    verify!(ch.c == '\u{4ffff}');
    let ba = BA {
        a: BIB {
            b1: false,
            b2: true,
            i: 123,
        },
    };
    let a = std::mem::transmute::<BA, A>(ba);
    verify!(a.x == 31488);
    verify!(a.y == 256);
}

pub unsafe fn t5(a: A) {
    let bib = std::mem::transmute::<A, BIB>(a);
    verify!(bib.b1 || (a.x % 256) == 0);
    verify!(bib.b2 || (a.y / 256) == 0);
    // todo: fix this
    //verify!(bib.i == (((a.x as u16 / 256) + ((a.y as u16 % 256) * 256)) as i16));
}

#[repr(C)]
pub struct FatPtr<T> {
    pub ptr: *const T,
    pub fat: usize,
}

pub unsafe fn t6() {
    let arr_ref: &[i32] = &[1, 2, 3];
    let arr_ptr = std::mem::transmute::<&[i32], *const [i32]>(arr_ref);
    let fat_ptr = std::mem::transmute::<*const [i32], FatPtr<i32>>(arr_ptr);
    verify!(fat_ptr.fat == 3);
    verify!(*fat_ptr.ptr == 1); //~ possible false verification condition
}

pub unsafe fn t7() {
    let arr_ref: &[i32] = &[1, 2, 3];
    let thin_ptr = arr_ref.as_ptr();
    let fat_ptr = FatPtr {
        ptr: thin_ptr,
        fat: 4,
    };
    let arr_ref2 = std::mem::transmute::<FatPtr<i32>, &[i32]>(fat_ptr);
    verify!(arr_ref2.len() == 4);
    verify!(arr_ref2[0] == 1);
    verify!(arr_ref2[1] == 2);
    verify!(arr_ref2[2] == 3);
    verify!(arr_ref2[3] == 666); //~ possible false verification condition
}

pub unsafe fn t8() {
    let char_arr = std::mem::transmute::<&str, &[u8]>("abc");
    verify!(char_arr.len() == 3);
    verify!(char_arr[0] == b'a');
    verify!(char_arr[1] == b'b');
    verify!(char_arr[2] == b'c');
}

pub fn main() {}
