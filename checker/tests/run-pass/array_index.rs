// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that visits the Place::Projection case of Visitor::visit_place
// and the ProjectionElem::Index case of Visitor::visit_projection_elem.

use mirai_annotations::*;

pub fn foo(arr: &mut [i32], i: usize) {
    arr[i] = 123; //~ possible index out of bounds
                  // If we get here i is known to be within bounds, so no warning below.
    bar(arr, i);
}

fn bar(arr: &mut [i32], i: usize) {
    arr[i] = 123;
    verify!(arr[i] == 123);
}

fn get_elem(arr: &[i32], i: usize) -> i32 {
    arr[i]
}

pub fn main() {
    let _x = 123; // make sure arr is not local 1
    let arr = [1, 2, 3];
    let elem = get_elem(&arr, 1);
    verify!(elem == 2);
}
