// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a closure that side-effects a mutable captured variable

use mirai_annotations::*;

fn foo<F>(f: F)
where
    F: FnOnce(),
{
    f()
}

pub fn main() {
    let mut x = 1;
    let f = || x += 1;
    foo(f);
    verify!(x == 2);
}
