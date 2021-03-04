// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//
// Tests that Cursor::read_to_end havocs the length of its parameter vector.

// use mirai_annotations::*;
// use std::io::{Cursor, Read, Result};
use std::io::Result;

pub fn t1(_buf: &[u8]) -> Result<()> {
    //todo: speed this up so that it passes on CI
    // let mut reader = Cursor::new(buf);
    // let mut v = Vec::with_capacity(1);
    // reader.read_to_end(&mut v)?;
    // verify!(v.len() == 0); // ~ possible false verification condition
    Ok(())
}

pub fn main() {}
