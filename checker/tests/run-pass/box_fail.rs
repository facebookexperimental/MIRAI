// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that creates a box with a failure path that calls box_free

pub fn test13(i: i64) {
    let _x = Box::new(-i); //~ possible attempt to negate with overflow
}

pub fn main() {}
