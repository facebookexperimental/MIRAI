// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses std::mem::transmute

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

pub fn main() {}
