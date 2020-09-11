// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that a left hand path is not refined as aggressively as a right hand path.
// In particular, if the left hand path is a local that binds to a reference, assignments
// to the path should update the binding, not the target of the bound reference.

use mirai_annotations::*;

pub fn t1() {
    let x = 1;
    let mut y = &x;
    verify!(*y == 1);
    let px = &x;
    let z = 2;
    y = &z;
    verify!(*px == 1);
    verify!(*y == 2);
}

fn t2a<'a>(a: &mut &'a i32, b: &'a i32) -> i32 {
    *a = b;
    1
}

pub fn t2() -> i32 {
    let x = 1;
    let mut y = &x;
    verify!(*y == 1);
    let px = &x;
    let z = 2;
    t2a(&mut y, &z);
    verify!(*px == 1);
    verify!(*y == 2);
    3
}

pub fn main() {}
