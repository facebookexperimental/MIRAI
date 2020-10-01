// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that calls visit_repeat

use mirai_annotations::*;

pub fn test1() {
    let x = [1; 2];
    verify!(x[0] == 1);
    verify!(x[1] == 1);
}

fn foo() -> [i32; 2] {
    [3; 2]
}

pub fn test2() {
    let x = foo();
    verify!(x[0] == 3);
    verify!(x[1] == 3);
}

fn bar(a: &mut [i32; 2]) {
    *a = [4; 2];
}

pub fn test3() {
    let mut x = [1; 2];
    bar(&mut x);
    verify!(x[0] == 4);
    verify!(x[1] == 4);
}

pub fn test4() {
    let mut x = [1, 2];
    bar(&mut x);
    verify!(x[0] == 4);
    verify!(x[1] == 4);
}

pub fn test5() {
    let mut x = [1; 2];
    x[0] = 3;
    bar(&mut x);
    verify!(x[0] == 4);
    verify!(x[1] == 4);
}

pub fn main() {}
