// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that creates and checks pointer offsets
#![feature(core_intrinsics)]

use mirai_annotations::*;

pub fn t1() {
    unsafe {
        let a = std::alloc::alloc(std::alloc::Layout::from_size_align(4, 2).unwrap());
        let _ = std::intrinsics::offset(a, -1); //~ effective offset is outside allocated range
    }
}

pub fn t2() {
    unsafe {
        let a = std::alloc::alloc(std::alloc::Layout::from_size_align(4, 2).unwrap());
        let b = std::intrinsics::arith_offset(a, -1);
        let _ = std::intrinsics::offset(b, 1);
    }
}

pub fn t3() {
    unsafe {
        let a = std::alloc::alloc(std::alloc::Layout::from_size_align(4, 2).unwrap());
        let b = std::intrinsics::arith_offset(a, -2);
        let _ = std::intrinsics::offset(b, 1); //~ effective offset is outside allocated range
    }
}

pub fn t4() {
    unsafe {
        let a = std::alloc::alloc(std::alloc::Layout::from_size_align(4, 2).unwrap());
        let _ = std::intrinsics::offset(a, 6); //~ effective offset is outside allocated range
    }
}

pub fn t5() {
    unsafe {
        let a = std::alloc::alloc(std::alloc::Layout::from_size_align(4, 2).unwrap());
        let _ = std::intrinsics::offset(a, 5);
    }
}

pub fn t6() {
    unsafe {
        let a1 = std::alloc::alloc(std::alloc::Layout::from_size_align(4, 2).unwrap());
        let a2 = std::alloc::realloc(a1, std::alloc::Layout::from_size_align(4, 2).unwrap(), 6);
        let _ = std::intrinsics::offset(a2, 6);
    }
}

pub fn t7() {
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
