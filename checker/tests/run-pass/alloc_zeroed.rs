// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that dereferenced uninitialized pointers into zeroed heap blocks known to be zero.

#![feature(core_intrinsics)]
use mirai_annotations::*;

pub fn t1() {
    unsafe {
        let pu8z = std::alloc::alloc_zeroed(std::alloc::Layout::from_size_align(4, 2).unwrap());
        verify!(*pu8z == 0);
        let pu8u = std::alloc::alloc(std::alloc::Layout::from_size_align(4, 2).unwrap());
        verify!(*pu8u == 0); //~ possible false verification condition
    }
}

pub fn t2() {
    unsafe {
        let z = std::alloc::alloc_zeroed(std::alloc::Layout::from_size_align(4, 2).unwrap());
        *z = 1;
        let pu8z = std::intrinsics::offset(z, 1);
        verify!(*pu8z == 0);
        let u = std::alloc::alloc(std::alloc::Layout::from_size_align(4, 2).unwrap());
        let pu8u = std::intrinsics::offset(u, 1);
        verify!(*pu8u == 0); //~ possible false verification condition
    }
}

pub fn t3() {
    unsafe {
        let z = std::alloc::alloc_zeroed(std::alloc::Layout::from_size_align(4, 2).unwrap());
        *z = 1;
        let pu8z = std::intrinsics::offset(z, 1);
        verify!(*pu8z == 0);
        let r = std::alloc::realloc(z, std::alloc::Layout::from_size_align(4, 2).unwrap(), 6);
        let pu8r = std::intrinsics::offset(r, 1);
        verify!(*pu8r == 0); //~ possible false verification condition
    }
}

pub fn main() {}
