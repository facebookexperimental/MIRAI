// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Checks that calls via traits can be resolved if call site has enough type information

// MIRAI_FLAGS --diag=library

use mirai_annotations::*;

pub trait Tr {
    fn bar(&self) -> i32;
}

struct Bar {
    i: i32,
}

impl Tr for Bar {
    fn bar(&self) -> i32 {
        self.i
    }
}

struct BarTwo {
    i: i32,
}

impl Tr for BarTwo {
    fn bar(&self) -> i32 {
        self.i * 2 //~ possible attempt to multiply with overflow
    }
}

struct Foo {
    bx: Box<dyn Tr>,
}

pub struct Foo2 {
    pub opt: Option<Box<dyn Tr>>,
}

pub fn t1() {
    let bar = Bar { i: 1 };
    let foo = Foo {
        bx: Box::new(bar) as Box<dyn Tr>,
    };
    // todo: fix this
    let bi = foo.bx.bar(); //~ the called function did not resolve to an implementation with a MIR body
    verify!(bi == 1);
}

pub fn t2(t: &dyn Tr) {
    let bi = t.bar();
    //~ the called function did not resolve to an implementation with a MIR body
    verify!(bi == 3); // ignored because the previous unresolved call makes every subsequent thing moot
}

pub fn t3() {
    let bar = Bar { i: 1 };
    let t = &bar as &dyn Tr;
    let bi = t3c(t);
    verify!(bi == 1);
}

fn t3c(t: &dyn Tr) -> i32 {
    t.bar()
}

// todo: fix this

// pub fn t4() {
//     let bar = Bar { i: 1 };
//     let foo = Foo {
//         bx: Box::new(bar) as Box<dyn Tr>,
//     };
//     let bi = t4c(foo);
//     verify!(bi == 1);
// }

// pub fn t4a() {
//     let bar = BarTwo { i: 1 };
//     let foo = Foo {
//         bx: Box::new(bar) as Box<dyn Tr>,
//     };
//     let bi = t4c(foo);
//     verify!(bi == 2);
// }

// fn t4c(foo: Foo) -> i32 {
//     foo.bx.bar()
// }

impl Clone for Box<dyn Tr> {
    fn clone(&self) -> Box<dyn Tr> {
        let bar = Bar { i: 1 };
        Box::new(bar) as Box<dyn Tr>
    }
}

pub fn t5() {
    let foo2 = Foo2 { opt: None };
    let c = foo2.opt.clone();
    verify!(c.is_none());
}

pub fn t6() {
    let foo2 = Foo2 { opt: None };
    let c = t6c(foo2);
    verify!(c.is_none());
}

pub fn t7(foo: Foo2) {
    let _c = t6c(foo); //~ possible incomplete analysis of call because of failure to resolve std::Clone::clone method
}

fn t6c(foo: Foo2) -> Option<Box<dyn Tr>> {
    foo.opt.clone() //~ related location
}

pub fn main() {}
