// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

#[macro_use]
extern crate mirai_annotations;

pub trait Tr {
    fn virt(&self) -> i32;
    fn actual(&self) -> i32 {
        self.virt()
    }
}

struct Foo {
    bar: i32,
}

impl Tr for Foo {
    fn virt(&self) -> i32 {
        self.bar
    }
}

pub fn main() {
    let foo = Foo { bar: 1 };
    verify!(foo.actual() == 1);
    verify!(foo.actual() == 2); //~ provably false verification condition
}
