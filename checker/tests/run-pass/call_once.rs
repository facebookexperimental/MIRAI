// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that calls a closure via FnOnce::call_once

use mirai_annotations::*;

fn call_once<F, T, V>(f: F, arg: (T, V)) -> T
where
    F: FnOnce((T, V)) -> T,
{
    f(arg)
}

pub fn main() {
    let f = |(x, _y)| x;
    let mut a = (9, 20);
    a.0 += 1;
    let b = (a, 30);
    let x = call_once(f, b);
    verify!(x.0 == 10);
    verify!(x.1 == 20);
}
