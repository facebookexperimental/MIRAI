// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a function summary.

fn foo() -> i32 { 123 }
fn bar(x: f32) -> f32 { x + 1.0 }
pub fn main() {
    debug_assert!(foo() == 123);
    debug_assert!(bar(1.0) == 2.0);
}
