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

pub fn subslice_pattern(from_start: bool) {
    let a = [[10], [20], [30]];
    if from_start {
        let [x @ .., _] = a;
        verify!(x[0][0] == 10);
        verify!(x[1][0] == 20);
    } else {
        let [_, y @ ..] = a;
        verify!(y[0][0] == 20);
        verify!(y[1][0] == 30);
    }
}
