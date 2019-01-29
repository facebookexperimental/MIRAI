// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that exercises the non numeric parts of visit_constant.

pub static A: bool = true;
pub static B: bool = false;
pub static C: char = 'A';
pub static D: &str = "foo";

pub fn main() {
    debug_assert!(A == true);
    debug_assert!(B == false);
    debug_assert!(C == 'A');
    //debug_assert!(D == "foo"); //todo: #2 enable this when we have summaries for the standard library
}
