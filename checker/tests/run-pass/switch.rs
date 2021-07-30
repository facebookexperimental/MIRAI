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

pub fn foo2(foo: Foo, too: u32) -> u32 {
    use Foo::*;
    match foo {
        Zero => 0u32.wrapping_add(too),
        One => 1u32.wrapping_add(too),
        Two => 2u32.wrapping_add(too),
        Three => 3u32.wrapping_add(too),
        Four => 4u32.wrapping_add(too),
        Five => 5u32.wrapping_add(too),
    }
}

pub fn main() {
    verify!(foo(Foo::Five) == 5);
    let too = abstract_value!(2);
    if too > 1 && too < 10 {
        verify!(foo2(Foo::Zero, too) > 1);
    }
}
