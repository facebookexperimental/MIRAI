// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that creates a box with a failure path that calls box_free

#![feature(box_syntax)]

pub fn test13(i: i64) {
    //todo: fix the bogus deallocation error by implementing size_of_val
    let _x = box -i; //~ possible attempt to negate with overflow
                     //~ possibly deallocates the pointer with layout information inconsistent with the allocation
}

pub fn main() {}
