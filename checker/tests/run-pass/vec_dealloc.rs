// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks layout consistency for vec alloc/dealloc

fn might_be_none(i: u8) -> Option<u8> {
    if i > 0 {
        Some(i)
    } else {
        None
    }
}

pub fn encode_key(i: u8) -> std::io::Result<Vec<u8>> {
    Ok(vec![
        might_be_none(i).ok_or(std::io::ErrorKind::InvalidInput)?
    ])
}

pub fn main() {}
