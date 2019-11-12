// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a cast in a verify condition.

#[macro_use]
extern crate mirai_annotations;

pub fn foo(i: u16) {
    if i > 16 {
        verify!((i as usize) > 16);
    }
}

pub fn main() {}
