// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that tracks slice lengths

pub struct NetworkStream {
    buffer: Vec<u8>,
}

impl NetworkStream {
    pub fn read_buffer(&mut self) {
        if self.buffer.len() < 4 {
            return;
        }

        let mut u32_bytes = [0; 4];
        u32_bytes.copy_from_slice(&self.buffer[0..4]);
        let _ = u32_bytes;
    }
}

pub fn main() {}
