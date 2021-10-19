// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses bit vectors in the SMT solver

use mirai_annotations::*;

pub fn write_u32_as_uleb128(binary: &mut Vec<u8>, value: u32) {
    let mut val = value;

    let v1: u8 = (val & 0x7f) as u8;
    if u32::from(v1) != val {
        binary.push(v1 | 0x80);
        val >>= 7;
    } else {
        binary.push(v1);
        return;
    }

    let v2: u8 = (val & 0x7f) as u8;
    if u32::from(v2) != val {
        binary.push(v2 | 0x80);
    } else {
        binary.push(v2);
    }
}

pub fn main() {
    let mut buf = Vec::<u8>::new();
    write_u32_as_uleb128(&mut buf, 129);
    //todo: more simplifications might allow the verify below to succeed
    verify!(buf.len() == 2); //~ possible false verification condition
                             //todo: find out why the above check causes the below one to become "provable" when it is clearly not
    verify!(buf.len() == 1); //~ provably false verification condition
}
