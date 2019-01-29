// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that visits the ProjectionElem::Subslice case of Visitor::visit_projection_elem

#![feature(box_syntax)]
#![feature(slice_patterns)]

pub fn main() {
    subslice_pattern(true);
    subslice_pattern(false);
}

pub fn subslice_pattern(from_start: bool) {
    let a = [[10], [20], [30]];
    if from_start {
        let [x.., _] = a;
        debug_assert!(x[0][0] == 10);
        debug_assert!(x[1][0] == 20);
    } else {
        let[_, y..] = a;
        debug_assert!(y[0][0] == 20);
        debug_assert!(y[1][0] == 30);
    }
}
