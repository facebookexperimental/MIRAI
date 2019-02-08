// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that promotes a constant to static memory by taking its address.

pub fn main() {
    let x = &1;
    let y = *x;
    debug_assert_eq!(y, 1);
}
