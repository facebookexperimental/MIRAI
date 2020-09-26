// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that verifies that s.is_empty() returns true for an empty string.

use mirai_annotations::*;

pub fn main() {
    let s = "";
    verify!(s.is_empty());
}
