// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that deallocations are valid and that further uses of deallocated
// pointers will lead to verification errors.

#![allow(internal_features)]
#![feature(core_intrinsics)]
use mirai_annotations::*;

pub fn t1() {
    unsafe {
        let layout = std::alloc::Layout::from_size_align(4, 2).unwrap();
        let a = std::alloc::alloc(layout);
        *a = 5;
        verify!(*a == 5);
        std::alloc::dealloc(a, layout);
        verify!(*a == 5); //~ possible false verification condition
    }
}

pub fn t2() {
    unsafe {
        let layout42 = std::alloc::Layout::from_size_align(4, 2).unwrap();
        let a = std::alloc::alloc(layout42);
        let layout82 = std::alloc::Layout::from_size_align(8, 2).unwrap();
        std::alloc::dealloc(a, layout82); //~ deallocates the pointer with layout information inconsistent with the allocation
    }
}

pub fn t2a() {
    unsafe {
        let layout42 = std::alloc::Layout::from_size_align(4, 2).unwrap();
        let a = std::alloc::alloc(layout42);
        let layout41 = std::alloc::Layout::from_size_align(4, 1).unwrap();
        std::alloc::dealloc(a, layout41); //~ deallocates the pointer with layout information inconsistent with the allocation
    }
}

pub fn t3() {
    unsafe {
        let layout = std::alloc::Layout::from_size_align(4, 2).unwrap();
        let a = std::alloc::alloc(layout);
        std::alloc::dealloc(a, layout);
        std::alloc::dealloc(a, layout); //~ the pointer points to memory that has already been deallocated
    }
}

pub fn t4() {
    unsafe {
        let layout42 = std::alloc::Layout::from_size_align(4, 2).unwrap();
        let a = std::alloc::alloc(layout42);
        let layout41 = std::alloc::Layout::from_size_align(4, 1).unwrap();
        let _ = std::alloc::realloc(a, layout41, 8); //~ reallocates the pointer with layout information inconsistent with the allocation
    }
}

pub fn t4a() {
    unsafe {
        let layout42 = std::alloc::Layout::from_size_align(4, 2).unwrap();
        let a = std::alloc::alloc(layout42);
        let layout82 = std::alloc::Layout::from_size_align(8, 2).unwrap();
        let _ = std::alloc::realloc(a, layout82, 16); //~ reallocates the pointer with layout information inconsistent with the allocation
    }
}

pub fn t5() {
    unsafe {
        let layout = std::alloc::Layout::from_size_align(4, 2).unwrap();
        let a = std::alloc::alloc(layout);
        std::alloc::dealloc(a, layout);
        let _ = std::alloc::realloc(a, layout, 8); //~ the pointer points to memory that has already been deallocated
    }
}

pub fn main() {}
