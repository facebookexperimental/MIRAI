// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses MIR constant array literals.

//todo: This is the only way I can find to generate such literals.
// Find out for sure if there is no other way.

use mirai_annotations::*;

fn g(x: &[u8], y: &[u8]) -> bool {
    x[0] == y[0]
}

fn f(value: &[u8]) -> bool {
    g(b"x", value)
}

pub fn main() {
    verify!(f(b"x"));
}
