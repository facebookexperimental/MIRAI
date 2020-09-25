// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that loops over a range with a filter.
// This checks that function constant arguments do not pollute summaries.

pub fn test() {
    for _i in (0..64usize).filter(|x| x % 2 == 1) {}
}

pub fn main() {}
