// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a function summary.

fn foo() -> i32 { 123 }
pub fn main() {
    debug_assert!(foo() == 123);
}
