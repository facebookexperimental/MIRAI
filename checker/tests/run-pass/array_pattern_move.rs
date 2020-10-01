// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that visits the ProjectionElem::Subslice case of Visitor::visit_projection_elem

use mirai_annotations::*;

pub fn main() {
    array_pattern(true);
    array_pattern(false);
}

struct Foo {
    f: i32,
}

pub fn array_pattern(from_end: bool) {
    let a = [Foo { f: 10 }, Foo { f: 20 }, Foo { f: 30 }, Foo { f: 40 }];
    if from_end {
        let [.., x, _] = a;
        verify!(x.f == 30);
    } else {
        let [_, y, ..] = a;
        verify!(y.f == 20);
    }
}
