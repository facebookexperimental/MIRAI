// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that visits the ProjectionElem::Subslice case of Visitor::visit_projection_elem

#![feature(box_syntax)]
#![feature(slice_patterns)]

pub fn main() {
    array_pattern(true);
    array_pattern(false);
}

pub fn array_pattern(from_end: bool) {
    let a = [[10], [20], [30], [40]];
    if from_end {
        let [.., x, _] = a;
        debug_assert!(x[0] == 30);
    } else {
        let[_, y, ..] = a;
        debug_assert!(y[0] == 20);
    }
}
