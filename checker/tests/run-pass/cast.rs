// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a cast in a verify condition.

use mirai_annotations::*;

fn foo(i: u16) {
    if i > 16 {
        verify!((i as usize) > 16);
    }
}

pub fn test1(i: u16) {
    foo(i);
}

fn bar(i: usize) {
    if i < 16 {
        verify!((i as u16) < 16);
    }
}

pub fn test2(i: usize) {
    bar(i);
}

pub fn main() {}
