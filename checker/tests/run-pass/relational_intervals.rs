// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Tests if intervals satisfy relational constraints

#[macro_use]
extern crate mirai_annotations;

pub fn t1(cond: bool) {
    let interval = if cond { -2 } else { 1000000 };
    verify!(interval <= 1000000);
    verify!(interval < 1000001);
    verify!(interval >= -2);
    verify!(interval > -3);
}

pub fn t2(cond: bool) {
    let interval = if cond { 0 } else { 10usize };
    let top = interval % 2;
    let raw = &cond as *const _;
    let bottom = interval - (raw as usize); //~ possible attempt to subtract with overflow
    verify!((interval as isize) > -2);
    verify!(top < 3);
    verify!(bottom <= bottom);
}

pub fn main() {}
