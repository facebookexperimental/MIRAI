// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a loop over an iterator.

pub fn to_be(dst: &mut [u16]) {
    for v in dst.iter_mut() {
        *v = v.to_be();
    }
}

pub fn main() {}
