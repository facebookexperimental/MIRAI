// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that calls Z3Solver::bv_variable with an explicit bit length different from the var type

pub fn read_uleb128_as_u32(bytes: [u8; 20]) -> u32 {
    let mut value: u32 = 0;
    let mut shift: u32 = 0;
    let mut cursor = 0;
    while cursor < bytes.len() {
        let byte = bytes[cursor];
        let val = byte & 0x7f;
        value |= (val as u32) << shift; //~ possible attempt to shift left with overflow
        if val == byte {
            return value;
        }
        shift += 7;
        if shift > 28 {
            break;
        }
        cursor += 1;
    }
    return value;
}

pub fn main() {}
