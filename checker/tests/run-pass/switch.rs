// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

use mirai_annotations::*;

pub enum Foo {
    Zero,
    One,
    Two,
    Three,
    Four,
    Five,
}

pub fn foo(foo: Foo) -> u32 {
    use Foo::*;
    match foo {
        Zero => 0,
        One => 1,
        Two => 2,
        Three => 3,
        Four => 4,
        Five => 5,
    }
}

pub fn main() {
    verify!(foo(Foo::Five) == 5);
}
