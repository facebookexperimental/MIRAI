// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that visits the ProjectionElem::Downcast case of Visitor::visit_projection_elem

use mirai_annotations::*;

pub enum Foo {
    Bar1(i32),
    Bar2(i32),
}

pub enum Zero {
    ZERO = 0,
}

pub fn dup(z: Zero) -> Zero {
    z
}

pub fn main() {
    let foo = Foo::Bar1(2);
    match foo {
        Foo::Bar1(x) => {
            verify!(x == 2);
        }
        _ => unreachable!(),
    }
}
