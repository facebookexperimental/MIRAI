// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that calls Z3Solver::bv_variable with an explicit bit length different from the var type.
// Additionally this also tests that the path condition includes equalities for loop controlled
// variables that are not explicitly included in the loop condition.

pub fn read_uleb128_as_u32(bytes: [u8; 20]) -> u32 {
    let mut value: u32 = 0;
    let mut shift: u32 = 0;
    let mut cursor = 0;
    while cursor < bytes.len() && shift <= 28 {
        let byte = bytes[cursor];
        let val = byte & 0x7f;
        value |= (val as u32) << shift;
        if val == byte {
            return value;
        }
        shift += 7;
        // todo: need some extra mechanism (such as narrowing) to propagate the
        // condition on shift back to the loop anchor
        // if shift > 28 {
        //     break;
        // }
        cursor += 1;
    }
    return value;
}

pub fn main() {}
