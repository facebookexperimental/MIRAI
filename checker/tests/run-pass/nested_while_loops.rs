// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//
// Tests a nested loop that uses a loop variable from the outer loop to modify the inner loop variable

use mirai_annotations::*;

pub fn main() {
    let mut i = 1;
    while i < 100 {
        verify!(i < 100);
        let mut j = i;
        while j <= 200 {
            verify!(i < 100 && j <= 200);
            j += i;
        }
        verify!(i < 100 && j > 200);
        i += 1;
    }
    verify!(i >= 100);
}
