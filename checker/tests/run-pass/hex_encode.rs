// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

use mirai_annotations::*;

const HEX_CHARS_LOWER: &[u8; 16] = b"0123456789abcdef";

fn byte2hex(byte: u8) -> (u8, u8) {
    let hi = HEX_CHARS_LOWER[((byte >> 4) & 0x0f) as usize];
    let lo = HEX_CHARS_LOWER[(byte & 0x0f) as usize];
    (hi, lo)
}

pub fn hex_encode(src: &[u8], dst: &mut [u8]) {
    for (byte, out) in src.iter().zip(dst.chunks_mut(2)) {
        let (hi, lo) = byte2hex(*byte);
        assume!(out.len() == 2);
        out[0] = hi;
        out[1] = lo;
    }
}

pub fn main() {}
