// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that invokes std::intrinsics::copy_nonoverlapping;

#![allow(internal_features)]
#![feature(core_intrinsics)]
use mirai_annotations::*;

pub fn t1() {
    let a = [1, 2, 3];
    let mut b = [4, 5, 6];
    unsafe {
        let aptr = a.as_ptr();
        verify!(*aptr == 1);
        let bptr = b.as_mut_ptr();
        std::intrinsics::copy_nonoverlapping(aptr, bptr, 2);
    }
    verify!(b[0] == 1);
    verify!(b[1] == 2);
    verify!(b[2] == 6);
}

fn t2copy(a: &[i32], b: &mut [i32]) {
    unsafe {
        let aptr = a.as_ptr();
        let bptr = b.as_mut_ptr();
        std::intrinsics::copy_nonoverlapping(aptr, bptr, 2);
    }
}

pub fn t2() {
    let a = [1, 2, 3];
    let mut b = [4, 5, 6];
    t2copy(&a, &mut b);
    verify!(a[0] == 1);
    verify!(a[1] == 2);
    verify!(a[2] == 3);
    verify!(b[0] == 1);
    verify!(b[1] == 2);
    verify!(b[2] == 6);
}

fn t3copy(a: &[i32], b: &mut [i32], count: usize) {
    unsafe {
        let aptr = a.as_ptr();
        let bptr = b.as_mut_ptr();
        std::intrinsics::copy_nonoverlapping(aptr, bptr, count);
    }
}

pub fn t3() {
    let a = [1, 2, 3];
    let mut b = [4, 5, 6];
    t3copy(&a, &mut b, 2);
    verify!(a[0] == 1);
    verify!(a[1] == 2);
    verify!(a[2] == 3);
    verify!(b[0] == 1);
    verify!(b[1] == 2);
    verify!(b[2] == 6);
}

fn t4copy_f<'a, F>(a: &mut [i32], b: &mut [i32], get_count: F)
where
    F: FnOnce() -> &'a usize,
{
    unsafe {
        let count = get_count();
        let aptr = a.as_mut_ptr();
        let bptr = b.as_mut_ptr();
        std::intrinsics::copy_nonoverlapping(aptr, bptr, *count);
    }
}

fn t4copy(a: &mut [i32], b: &mut [i32], count: usize) {
    t4copy_f(a, b, || &count)
}

pub fn t4() {
    let mut a = [1, 2, 3];
    let mut b = [4, 5, 6];
    t4copy(&mut b, &mut a, 2);
    verify!(a[0] == 4);
    verify!(a[1] == 5);
    verify!(a[2] == 3);
    verify!(b[0] == 4);
    verify!(b[1] == 5);
    verify!(b[2] == 6);
}

pub fn main() {}
