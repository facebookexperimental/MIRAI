// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses intrinsics::write_bytes

use mirai_annotations::*;

fn foo<T>(a: &mut [T; 2]) {
    unsafe {
        let ptr = a.as_mut_ptr();
        std::ptr::write_bytes(ptr, 0xfe, 2);
    }
}

pub fn t1() {
    let mut a = [1u8, 2u8];
    foo(&mut a);
    verify!(a[0] == 0xfe);
    verify!(a[1] == 0xfe);
}

pub fn t2() {
    let mut a = [1u16, 2u16];
    foo(&mut a);
    verify!(a[0] == 0xfefe);
    verify!(a[1] == 0xfefe);
}

fn foo2<T>(b: &mut T) {
    unsafe {
        let ptr = std::mem::transmute::<&mut T, *mut T>(b);
        std::ptr::write_bytes(ptr, 0xfe, 4);
    }
}

struct Bar {
    one: u32,
}

pub fn t3() {
    let mut b = Bar { one: 2u32 };
    foo2(&mut b);
    verify!(b.one == 0xfefefefe);
}

struct Bas {
    one: u16,
    two: u8,
    three: u8,
}

pub fn t4() {
    let mut b = Bas {
        one: 1u16,
        two: 2u8,
        three: 3u8,
    };
    foo2(&mut b);
    verify!(b.one == 0xfefe);
    verify!(b.two == 0xfe);
    verify!(b.three == 0xfe);
}

pub fn t5() {
    let mut t = (1u16, 2u16);
    foo2(&mut t);
    verify!(t.0 == 0xfefe);
    verify!(t.1 == 0xfefe);
}

fn foo3(a: &mut [u8], n: usize) {
    a[0] = 99;
    unsafe {
        let b = &mut a[1..];
        let ptr = b.as_mut_ptr();
        std::ptr::write_bytes(ptr, 0xfe, n);
    }
}

pub fn t6() {
    let mut a = [1u8, 2u8, 3u8];
    foo3(&mut a[0..3], 2);
    verify!(a[0] == 99);
    verify!(a[1] == 0xfe);
    verify!(a[2] == 0xfe);
}

fn foo4(a: &mut [u8], n: usize) {
    a[n] = 99;
    unsafe {
        let ptr = a.as_mut_ptr();
        std::ptr::write_bytes(ptr, 0xfe, n);
    }
}

pub fn t7() {
    let mut a = [1u8, 2u8, 3u8];
    foo4(&mut a[0..3], 2);
    verify!(a[0] == 0xfe);
    verify!(a[1] == 0xfe);
    verify!(a[2] == 99);
}

pub fn main() {}
