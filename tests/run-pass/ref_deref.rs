// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses PathSelector::Deref and ExpressionDomain::Reference

pub fn main() {
    let a: &[i32] = &[10, 20];
    let n = 1;
    let m = &n;
    debug_assert!(*m == 1);
    debug_assert!(a[*m] == 20);
}
