// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that drop handlers are correctly analyzed

use mirai_annotations::*;

struct Guard<'a> {
    i: &'a mut i32,
}

impl Drop for Guard<'_> {
    fn drop(&mut self) {
        *self.i = 100;
    }
}

fn call_guard(i: &mut i32) {
    let _ = Guard { i };
}

pub fn t1() {
    let mut i = 10;
    call_guard(&mut i);
    verify!(i == 100);
}

pub fn main() {}
