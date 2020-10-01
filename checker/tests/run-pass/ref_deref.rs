// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses PathSelector::Deref and Expression::Reference

use mirai_annotations::*;

pub fn main() {
    let a: &[i32] = &[10, 20];
    let n = 1;
    let m = &n;
    verify!(*m == 1);
    verify!(a[*m] == 20);
}
