// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that visits the Place::Static case of Visitor::visit_place

pub static mut A: isize = 3;

pub fn main() {
    unsafe { A = 4; }
}

pub fn foo() -> isize {
    unsafe { A.clone() }
}
