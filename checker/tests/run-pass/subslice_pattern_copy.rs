// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that visits the ProjectionElem::Subslice case of Visitor::visit_projection_elem

#![feature(slice_patterns)]

#[macro_use]
extern crate mirai_annotations;

pub fn main() {
}

pub fn subslice_pattern() {
    let a = [[10], [20], [30]];
    let [x @ .., _] = a;
    verify!(x[0][0] == 10);
}
