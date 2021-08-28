// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses computed constants.

use mirai_annotations::*;

pub struct AsciiSet {
    mask: [Chunk; ASCII_RANGE_LEN / BITS_PER_CHUNK],
}

type Chunk = u32;

const ASCII_RANGE_LEN: usize = 0x80;

const BITS_PER_CHUNK: usize = 8 * std::mem::size_of::<Chunk>();

impl AsciiSet {
    /// Called with UTF-8 bytes rather than code points.
    /// Not used for non-ASCII bytes.
    const fn contains(&self, byte: u8) -> bool {
        let chunk = self.mask[byte as usize / BITS_PER_CHUNK];
        let mask = 1 << (byte as usize % BITS_PER_CHUNK);
        (chunk & mask) != 0
    }

    pub const fn add(&self, byte: u8) -> Self {
        let mut mask = self.mask;
        mask[byte as usize / BITS_PER_CHUNK] |= 1 << (byte as usize % BITS_PER_CHUNK);
        AsciiSet { mask }
    }
}

pub fn t1() {
    let s = AsciiSet { mask: [0, 0, 0, 0] };
    let s1 = s.add(1);
    verify!(s1.contains(1));
}

pub fn main() {}
