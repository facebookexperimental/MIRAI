// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks various simplifications

use mirai_annotations::*;

pub fn f1(b: bool) {
    verify!(b || !b);
    verify!(!b || b);
}

pub fn f2(x: bool, y: bool) {
    let z = (x || y) && x;
    verify!(z == x);
    let z = (x || y) && y;
    verify!(z == y);
}

pub fn f3(x: bool, y: bool) {
    let z = (x || y) && (!x);
    verify!(z == y && !x); //~ possible false verification condition
}

pub fn f4(x: bool, y: bool) {
    let z = (x || y) && (!y);
    verify!(z == x && !y); //~ possible false verification condition
}

pub fn f5(x: bool, y: bool) {
    let z = (x && y) || x;
    verify!(z == x);
}

pub fn f6(x: bool, y: bool) {
    let z = (x && y) || y;
    verify!(z == y);
}

pub fn f7(x: bool, y: bool) {
    let z = (x && !y) || y;
    verify!(z == (y || x));
}

pub fn f8(x: bool, y: bool, a: i32, b: i32) {
    let z = if x || y {
        if x {
            a
        } else {
            b
        }
    } else {
        b
    };
    verify!(z == if x { a } else { b });
}

pub fn f9(x: bool, y: bool, a: i32, b: i32) {
    let z = if x || y {
        if y {
            a
        } else {
            b
        }
    } else {
        b
    };
    verify!(z == if y { a } else { b });
}

pub fn f10(x: bool, y: bool, a: i32, b: i32) {
    let z = if x || y {
        if x {
            a
        } else {
            b
        }
    } else {
        a
    };
    verify!(z == if y { b } else { a }); //~ possible false verification condition
}

pub fn f11(x: bool, y: bool, a: i32, b: i32) {
    let z = if x || y {
        if y {
            a
        } else {
            b
        }
    } else {
        a
    };
    verify!(z == if x { b } else { a }); //~ possible false verification condition
}

pub fn main() {}
