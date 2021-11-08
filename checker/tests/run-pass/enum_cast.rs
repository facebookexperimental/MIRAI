// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that casts an enum value to an unsigned integer value

use mirai_annotations::*;

enum Foo {
    BarOne = 1,
    BarTwo = 2,
}

fn t1a(foo: Foo) -> u8 {
    foo as u8
}

fn t1b(b: bool) -> u8 {
    if b {
        t1a(Foo::BarOne)
    } else {
        t1a(Foo::BarTwo)
    }
}

pub fn t1() {
    let n = t1b(true);
    verify!(n == 1);
}

pub fn main() {}
