// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that exercises visit_used_copy with a structured value.

use mirai_annotations::*;

#[derive(Clone, Copy)]
struct Point {
    pub x: i32,
    pub y: i32,
}

pub fn test() {
    let p = Point { x: 1, y: 2 };
    let mut q = p;
    q.x = 3;
    verify!(p.x == 1);
    verify!(p.y == 2);
    verify!(q.x == 3);
    verify!(q.y == 2);
}
