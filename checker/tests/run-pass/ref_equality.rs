// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks if references can be compared

use mirai_annotations::*;

pub fn main() {
    let a = &1;
    verify!(a == &1);
}
