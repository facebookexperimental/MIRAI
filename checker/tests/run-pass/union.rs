// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that a value is tracked through a union.

use mirai_annotations::*;

pub const fn as_bytes(_self: &str) -> &[u8] {
    union Slices<'a> {
        str: &'a str,
        slice: &'a [u8],
    }
    unsafe { Slices { str: _self }.slice }
}

pub fn main() {
    let bytes = as_bytes("abc");
    verify!(bytes.len() == 3);
    let byte_0 = bytes[0];
    verify!(byte_0 == b'a');
}
