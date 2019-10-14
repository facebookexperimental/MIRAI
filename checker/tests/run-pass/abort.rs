// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that calls Visitor::visit_abort

use std::panic;

pub extern "C" fn panic_in_ffi() {
    panic!("Test"); //~ Test
}

pub fn main() {}
