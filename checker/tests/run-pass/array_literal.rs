// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that calls visit_aggregate

use mirai_annotations::*;

pub fn main() {
    let x = [1, 2];
    verify!(x[0] == 1);
    verify!(x[1] == 2);
}
