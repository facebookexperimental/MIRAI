// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that visits the Place::Projection case of Visitor::visit_place
// and the ProjectionElem::Index case of Visitor::visit_projection_elem.

pub fn foo(arr: &mut [i32], i: usize) {
    arr[i] = 123;
}
