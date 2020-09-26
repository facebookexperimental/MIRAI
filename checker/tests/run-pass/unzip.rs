// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that calls Iterator::unzip

use mirai_annotations::*;

pub fn test() {
    let a = [(1, 2), (3, 4)];

    let (left, right): (Vec<_>, Vec<_>) = a.iter().cloned().unzip();
    //todo: fix the false messages below
    verify!(left == [1, 3]); //~ provably false verification condition
    verify!(right == [2, 4]); //~ provably false verification condition
}

pub fn main() {}
