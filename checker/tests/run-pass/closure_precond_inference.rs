// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test which checks whether constraints are propagated for captured values.

use mirai_annotations::*;

pub fn main() {
    call(1);
}

fn call(x: i32) {
    checked_assume!(x > 0);
    let f = || {
        assert!(x > 0);
    };
    f()
}
