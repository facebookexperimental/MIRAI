// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that we don't repeat possible.

pub fn foo(i: i32) {
    bar(i); //~ possible foo_bar
}

pub fn bar(i: i32) {
    assert!(i > -123, "foo_bar"); //~ related location
}

pub fn main() {}
