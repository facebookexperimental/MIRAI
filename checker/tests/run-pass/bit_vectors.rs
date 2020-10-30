// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses bit vectors in the SMT solver

fn write_u32_as_uleb128(value: u32) {
    let mut val = value;
    let v1: u8 = (val & 0x7f) as u8;
    assert!(v1 == 1);
    val >>= 7;
    let v2: u8 = (val & 0x7f) as u8;
    assert!(v2 == 1);
}

fn write_i32_as_uleb128(value: i32) {
    let mut val = value;
    let v1: u8 = (val & (-127)) as u8;
    assert!(v1 == 1);
    val >>= 7;
    let v2: u8 = (val & (-127)) as u8;
    assert!(v2 == 128);
}

pub fn main() {
    write_u32_as_uleb128(129);
    write_i32_as_uleb128(-129);
}
