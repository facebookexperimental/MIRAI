// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// This test updates an offset inside a loop to check that a fixpoint is reached when using offsets

use mirai_annotations::*;

const WORDS: usize = 25;

pub struct Buffer([u64; WORDS]);

impl Buffer {
    fn execute<F: FnOnce(&mut [u8])>(&mut self, offset: usize, len: usize, f: F) {
        let buffer: &mut [u8; WORDS * 8] = unsafe { core::mem::transmute(&mut self.0) };
        f(&mut buffer[offset..][..len]);
    }

    pub fn xorin(&mut self, src: &[u8], offset: usize, len: usize) {
        precondition!(offset < self.0.len() * 8);
        self.execute(offset, len, |dst| {
            let len = dst.len();
            let mut dst_ptr = dst.as_mut_ptr();
            let mut src_ptr = src.as_ptr();
            for _ in 0..len {
                unsafe {
                    *dst_ptr ^= *src_ptr;
                    src_ptr = src_ptr.offset(1);
                    dst_ptr = dst_ptr.offset(1);
                }
            }
        });
    }
}

pub fn main() {}
