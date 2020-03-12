// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that does a weak update of an array element

#[macro_use]
extern crate mirai_annotations;

pub fn test(i: usize) {
    precondition!(i < 3);
    let mut a = [3, 4, 5];
    a[i] = 666;
    verify!(a[i] == 666);
    verify!(a[0] == 3 || a[0] == 666);
    if i != 0 {
        verify!(a[0] == 3);
    } else {
        verify!(a[0] == 3); //~ provably false verification condition
    }
}

pub fn main() {}
