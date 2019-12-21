// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses bit vectors in the SMT solver

#[macro_use]
extern crate mirai_annotations;

fn write_u32_as_uleb128(value: u32) {
    let mut val = value;
    let v1: u8 = (val & 0x7f) as u8;
    verify!(v1 == 1);
    val >>= 7;
    let v2: u8 = (val & 0x7f) as u8;
    verify!(v2 == 1);
}

pub fn main() {
    write_u32_as_uleb128(129);
}
