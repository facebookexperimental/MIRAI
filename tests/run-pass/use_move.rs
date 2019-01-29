// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that exercises visit_used_move with a structured value.

struct Point {
    pub x: i32,
    pub y: i32,
}

pub fn test() {
    let p = Point { x: 1, y: 2};
    let q = p;
    debug_assert!(q.x == 1);
    debug_assert!(q.y == 2);
}
