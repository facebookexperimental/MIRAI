// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that exercises visit_used_move with a structured value.

use mirai_annotations::*;

struct Point {
    pub x: i32,
    pub y: i32,
}

pub fn test() {
    let p = Point { x: 1, y: 2 };
    let q = p;
    verify!(q.x == 1);
    verify!(q.y == 2);
}
