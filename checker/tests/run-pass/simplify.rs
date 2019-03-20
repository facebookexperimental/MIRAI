// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks various simplifications

#[macro_use]
extern crate mirai_annotations;

pub fn main() {
    foo(true);
}

fn foo(b: bool) {
    verify!(b || !b);
    verify!(!b || b);
}
