// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that assume_preconditions! works

use mirai_annotations::*;

pub fn main() {
    assume_preconditions!();
    foo(1);
}

fn foo(i: i32) {
    precondition!(i != 1);
}
