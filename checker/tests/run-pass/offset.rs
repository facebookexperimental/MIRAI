// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that creates and checks pointer offsets
#![feature(core_intrinsics)]

use mirai_annotations::*;

pub fn t1() -> u8 {
    unsafe {
        let a = std::alloc::alloc(std::alloc::Layout::from_size_align(4, 2).unwrap());
        let b = std::intrinsics::offset(a, -1); //~ effective offset is outside allocated range
        *b
    }
}

pub fn t2() -> u8 {
    unsafe {
        let a = std::alloc::alloc(std::alloc::Layout::from_size_align(4, 2).unwrap());
        let b = std::intrinsics::arith_offset(a, -1);
        let c = std::intrinsics::offset(b, 1);
        *c
    }
}

pub fn t3() -> u8 {
    unsafe {
        let a = std::alloc::alloc(std::alloc::Layout::from_size_align(4, 2).unwrap());
        let b = std::intrinsics::arith_offset(a, -2);
        let c = std::intrinsics::offset(b, 1); //~ effective offset is outside allocated range
        *c
    }
}

pub fn t4() -> u8 {
    unsafe {
        let a = std::alloc::alloc(std::alloc::Layout::from_size_align(4, 2).unwrap());
        let b = std::intrinsics::offset(a, 6); //~ effective offset is outside allocated range
        *b
    }
}

pub fn t5() -> u8 {
    unsafe {
        let a = std::alloc::alloc(std::alloc::Layout::from_size_align(4, 2).unwrap());
        let b = std::intrinsics::offset(a, 5);
        *b
    }
}

pub fn t6() -> u8 {
    unsafe {
        let a1 = std::alloc::alloc(std::alloc::Layout::from_size_align(4, 2).unwrap());
        let a2 = std::alloc::realloc(a1, std::alloc::Layout::from_size_align(4, 2).unwrap(), 6);
        let a3 = std::intrinsics::offset(a2, 6);
        *a3
    }
}

fn t7a(i: isize) -> u8 {
    unsafe {
        let a = std::alloc::alloc(std::alloc::Layout::from_size_align(4, 2).unwrap());
        let o1 = std::intrinsics::offset(a, 1) as *mut u8;
        *o1 = 111;
        let o2 = std::intrinsics::offset(a, i) as *mut u8;
        *o2 = 111 & (i as u8);
        *o1
    }
}

pub fn t7() {
    let r = t7a(1);
    verify!(r == 1);
}

pub fn t8() {
    unsafe {
        let a1 = std::alloc::alloc(std::alloc::Layout::from_size_align(4, 2).unwrap()) as *mut u8;
        *a1 = 111;
        let mut a2 = a1;
        let mut i: isize = 1;
        while i < 2 {
            a2 = std::intrinsics::offset(a1, i) as *mut u8;
            *a2 = 222;
            i += 1;
        }
        verify!(*a1 == 111);
        //todo: figure out how to verify this
        verify!(*a2 == 222); //~ possible false verification condition
    }
}

pub fn main() {}
