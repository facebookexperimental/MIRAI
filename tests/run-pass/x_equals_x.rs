// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks if expressions like x == x can be simplified.

pub fn main() {
    foo(1, 2.0);
}

fn foo (x: i32, y: f32) {
    if x == x {
        debug_assert!(true);
    } else {
        debug_assert!(false);
    }
    if y == y {
        debug_assert!(true);
    } else {
        debug_assert!(false);  //~ could not prove assertion: false
    }
}
