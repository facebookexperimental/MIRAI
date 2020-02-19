// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that creates and checks pointer offsets
#![feature(core_intrinsics)]

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

pub fn main() {}
