// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a true assertion

use mirai_annotations::*;

pub fn test_assert() {
    let i = 1;
    verify!(i == 1);
}
