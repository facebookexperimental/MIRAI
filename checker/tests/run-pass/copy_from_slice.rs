// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

#![allow(internal_features)]
#![feature(core_intrinsics)]
use mirai_annotations::*;

// A test that does a slice to slice copy where the underlying storage of the target slice is
// not the same length as the source slice.

pub fn to_bytes(r: [u8; 4]) -> [u8; 8] {
    let mut signature_bytes: [u8; 8] = [0u8; 8];

    signature_bytes[..4].copy_from_slice(&r[..]);
    signature_bytes
}

pub fn test() {
    let r = [1u8; 4];
    let mut signature_bytes: [u8; 8] = [0u8; 8];

    signature_bytes[..4].copy_from_slice(&r[..]);
    verify!(signature_bytes[0] == 1);
}

pub fn main() {}
