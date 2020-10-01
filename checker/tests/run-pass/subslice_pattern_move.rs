// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that visits the ProjectionElem::Subslice case of Visitor::visit_projection_elem

use mirai_annotations::*;

pub fn main() {
    subslice_pattern(true);
    subslice_pattern(false);
}

struct Foo {
    f: i32,
}

pub fn subslice_pattern(from_start: bool) {
    let a = [Foo { f: 10 }, Foo { f: 20 }, Foo { f: 30 }];
    if from_start {
        let [x @ .., _] = a;
        verify!(x[0].f == 10);
        verify!(x[1].f == 20);
    } else {
        let [_, y @ ..] = a;
        verify!(y[0].f == 20);
        verify!(y[1].f == 30);
    }
}
