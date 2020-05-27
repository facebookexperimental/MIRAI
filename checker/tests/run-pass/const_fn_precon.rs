// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that public const functions do not need explicit preconditions
// since those involve code that the Rust compiler does not like in constant functions.

pub const fn foo(x: i32) -> i32 {
    x + 1 //~ related location
}

pub fn main() {
    foo(2);
    foo(i32::MAX); //~ attempt to add with overflow
}
