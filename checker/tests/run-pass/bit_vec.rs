// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks relaxed mode preconditions for conditions that overflow in size

// MIRAI_FLAGS --diag=default

pub struct BitVec {
    inner: Vec<u8>,
}
const BUCKET_SIZE: usize = 8;

impl BitVec {
    pub fn set(&mut self, pos: u8) {
        let bucket: usize = pos as usize / BUCKET_SIZE;
        if self.inner.len() <= bucket {
            self.inner.resize(bucket + 1, 0);
        }
        let bucket_pos = pos as usize - (bucket * BUCKET_SIZE);
        self.inner[bucket] |= 0b1000_0000 >> bucket_pos as u8;
    }
}

pub fn main() {}
