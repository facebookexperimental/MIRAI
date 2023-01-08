// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that adds a precondition to an async function

use mirai_annotations::*;

async fn foo(i: i32, j: i32) -> i32 {
    precondition!(i > j); // ~ related location
    i - j
}

pub fn main() {
    let _ = foo(10, 3);
    // todo: fix this
    let _ = foo(1, 2); // ~ unsatisfied precondition
}
