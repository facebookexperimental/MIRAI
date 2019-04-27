// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//
// Tests a nested loop that uses a loop variable from the outer loop to modify the inner loop variable

pub fn main() {
    let mut i = 1;
    while i < 100 {
        let mut j = i;
        while j <= 100 {
            j += i; //~ possible attempt to add with overflow
        }
        i += 1; //~ possible attempt to add with overflow
    }
}
