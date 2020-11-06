// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that exercises the non numeric parts of visit_constant.

use mirai_annotations::*;

pub enum Foo {
    Bar,
    Bas,
}

pub fn get_bar() -> Foo {
    Foo::Bar
}

pub static A: bool = true;
pub static B: bool = false;
pub static C: char = 'A';
pub static D: &str = "foo";

pub fn main() {
    verify!(A == true);
    verify!(B == false);
    verify!(C == 'A');
    verify!(D == "foo");
    verify!(if let Foo::Bar = get_bar() {
        true
    } else {
        false
    });
}
