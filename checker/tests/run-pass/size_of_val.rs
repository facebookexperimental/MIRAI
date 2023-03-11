// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

use std::mem;

use mirai_annotations::*;

pub fn test1() {
    verify!(mem::size_of_val(&5i32) == 4);

    let x: [u8; 13] = [0; 13];
    let y: &[u8] = &x;
    verify!(mem::size_of_val(y) == 13);
}

pub fn trait_test() {
    let x: &dyn PartialEq<u16> = &123u16;
    verify!(mem::size_of_val(x) == 2); //~ possible false verification condition
}

pub fn main() {}
