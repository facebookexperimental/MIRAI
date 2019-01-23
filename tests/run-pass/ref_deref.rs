// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses PathSelector::Deref and ExpressionDomain::Reference

pub fn foo(a: &[i32]) {
    let n = 1;
    let m = &n;
    let _k = *m;
    let _e = a[*m];
}
