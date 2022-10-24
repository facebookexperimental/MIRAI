// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// MIRAI_FLAGS --test_only

use mirai_annotations::*;

pub trait Tr<T> {
    fn virt(&self) -> T;
    fn actual(&self) -> T {
        self.virt()
    }
}

struct Foo {
    bar: i32,
}

impl Tr<i32> for Foo {
    fn virt(&self) -> i32 {
        self.bar
    }
}

#[test]
pub fn t1() {
    let foo = Foo { bar: 1 };
    verify!(foo.actual() == 1);
    // todo: fix this
    verify!(foo.actual() == 2); // ~ provably false verification condition
}

pub fn main() {}
