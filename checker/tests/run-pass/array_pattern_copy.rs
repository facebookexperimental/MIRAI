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

pub fn array_pattern(from_end: bool) {
    let a = [[10], [20], [30], [40]];
    if from_end {
        let [.., x, _] = a;
        verify!(x[0] == 30);
    } else {
        let [_, y, ..] = a;
        verify!(y[0] == 20);
    }
}
