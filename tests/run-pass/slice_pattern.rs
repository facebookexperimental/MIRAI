// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that visits the ProjectionElem::ConstantIndex case of Visitor::visit_projection_elem

pub fn foo(arr: &mut [i32]) {
    match arr {
        [x, _] => *x = 5,
        _ => (),
    }
}


