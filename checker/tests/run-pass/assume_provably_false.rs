// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that a provably false assumption is ignored

use mirai_annotations::*;

pub fn main() {
    let a = 5;
    assume!(a < 5); //~ assumption is provably false and it will be ignored
    verify!(a < 5); //~ provably false verification condition
}
