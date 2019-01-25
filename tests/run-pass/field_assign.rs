// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that visits the ProjectionElem::Field case of Visitor::visit_projection_elem

pub struct Test {
    pub field: usize
}

pub fn foo(t: &mut Test) {
    t.field = 123;
    debug_assert!(t.field == 123);
}
