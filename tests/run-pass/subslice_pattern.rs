// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that visits the ProjectionElem::Subslice case of Visitor::visit_projection_elem

#![feature(box_syntax)]
#![feature(slice_patterns)]

pub fn subslice_pattern_from_end(arg: bool) {
    let a = [String::from("a"), String::from("a"), String::from("a")];
    if arg {
        let[.., _x, _] = a;
    } else {
        let[_, _y..] = a;
    }
}
