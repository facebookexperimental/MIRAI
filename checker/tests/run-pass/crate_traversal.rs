// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// statements and expressions that exercise all visitor code paths

#![allow(unused)]
#![feature(generators)]

use mirai_annotations::*;

use std::arch::asm;
use std::mem;

pub trait TestTrait {
    fn test_method() {
        let _loc = [1];
        let loc2 = [0; 512];
    }
}

pub struct TestStruct {
    pub test_field: i64,
}

impl TestStruct {
    pub fn test_function() {}
    pub fn test_method(&self) {}
}

pub unsafe fn test1() {
    #[derive(Copy, Clone)]
    enum Void {}
    union A {
        a: (),
        v: Void,
    }
    let a = A { a: () };
    match a.v {}
}

fn test2() {
    let z = 0;
    let _x = { &z };
}

fn test3() {
    let nodrop_x = false;
    let _nodrop_y;

    // Since boolean does not require drop, this can be a simple
    // assignment:
    _nodrop_y = nodrop_x;

    let drop_x: Option<Box<u32>> = None;
    let _drop_y;

    // Since the type of `drop_y` has drop, we generate a `replace`
    // terminator:
    _drop_y = drop_x;
}

fn test4() {
    let mut should_break = false;
    loop {
        if should_break {
            break;
        }
        should_break = true;
    }
}

pub fn test5() {
    unsafe {
        asm!("NOP") //~ Inline assembly code cannot be analyzed by MIRAI.
    }
}

fn test6() {
    println!("{}", bar());
}

#[inline(always)]
fn foo(x: &i32, y: &i32) -> bool {
    *x == *y
}

fn bar() -> bool {
    let f = foo;
    f(&1, &-1)
}

fn test7() {
    loop {
        let beacon = {
            match true {
                false => 4,
                true => break,
            }
        };
        drop(&beacon);
    }
}

fn test8(x: &mut i32, y: &mut i32) -> i32 {
    *x = 42;
    *y = 7;
    *x // Will load 42! We can optimize away the load.
}

struct Test(i32);

impl Test {
    // Make sure we run the pass on a method, not just on bare functions.
    fn foo<'x>(&self, x: &'x mut i32) -> &'x mut i32 {
        x
    }
    fn foo_shr<'x>(&self, x: &'x i32) -> &'x i32 {
        x
    }
}

fn test9() {
    let mut x = 0;
    {
        let v = Test(0).foo(&mut x); // just making sure we do not panic when there is a tuple struct ctor
        let w = { v }; // assignment
        let w = w; // reborrow
                   // escape-to-raw (mut)
        let _w = w as *mut _;
    }

    // Also test closures
    let c: fn(&i32) -> &i32 = |x: &i32| -> &i32 {
        let _y = x;
        x
    };
    let _w = c(&x);

    // need to call `foo_shr` or it doesn't even get generated
    Test(0).foo_shr(&0);

    // escape-to-raw (shr)
    let _w = _w as *const _;
}

fn test10() {
    let _a = || {
        yield;
        let a = String::new();
        a.len()
    };
}

pub fn test11(arr: &[String]) {
    let e = &arr[1]; //~ possible index out of bounds
}

#[allow(arithmetic_overflow)]
pub fn test12() {
    let x = 200u8 * 4; //~ attempt to multiply with overflow
}

fn test13(a: i32, b: i32) -> Option<i32> {
    Some(a.checked_add(1)?.checked_mul(3_i32.checked_add(b)?)?)
}

fn main() {}
