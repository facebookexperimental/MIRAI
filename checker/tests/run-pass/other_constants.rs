// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that exercises the non numeric parts of visit_constant.

#[macro_use]
extern crate mirai_annotations;

pub static A: bool = true;
pub static B: bool = false;
pub static C: char = 'A';
pub static D: &str = "foo";

pub fn main() {
    verify!(A == true);
    verify!(B == false);
    verify!(C == 'A');
    //verify!(D == "foo"); //todo: #2 enable this when we have summaries for the standard library
}
