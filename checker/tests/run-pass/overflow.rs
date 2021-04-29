// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

use mirai_annotations::*;
use std::io::{Cursor, Read};

pub fn read_to_end(r: &mut Cursor<&[u8]>, buf: &mut Vec<u8>) {
    let mut len = buf.len();
    loop {
        match r.read(&mut buf[len..]) {
            Ok(n) => {
                assume!(len < usize::MAX - n);
                len += n
            }
            Err(..) => {
                break;
            }
        }
    }
}

pub fn main() {}
