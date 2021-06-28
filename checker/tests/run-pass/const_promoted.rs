// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that visits the Place::Promoted case in Visitor::visit_place

const FLOAT1_AS_I32: i32 = 1065353216;

pub fn main() {
    match &FLOAT1_AS_I32 {
        x => *x,
    };
}
