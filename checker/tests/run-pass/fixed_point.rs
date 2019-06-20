// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that regresses a fixed point divergence bug

pub fn write_u32_as_uleb128(value: u32) {
    let mut val = value;
    loop {
        let v: u8 = (val & 0x7f) as u8;
        if (v as u32) != val {
            val >>= 7;
        } else {
            break;
        }
    }
}

pub fn main() {}
