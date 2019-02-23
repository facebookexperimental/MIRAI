// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Tests if intervals satisfy relational constraints

pub fn t1(cond: bool) {
    let interval = if cond { -2 } else { 1000000 };
    debug_assert!(interval <= 1000000);
    debug_assert!(interval < 1000001);
    debug_assert!(interval >= -2);
    debug_assert!(interval > -3);
}

pub fn t2(cond: bool) {
    let interval = if cond { 0 } else { 10usize };
    let top = interval % 2;
    let raw = &cond as *const _;
    let bottom = interval - (raw as usize); //~ possible attempt to subtract with overflow
    debug_assert!((interval as isize) > -2);
    debug_assert!(top < 3); //~ could not prove assertion: top < 3
    debug_assert!(bottom <= bottom); //~ could not prove assertion: bottom <= bottom
}

