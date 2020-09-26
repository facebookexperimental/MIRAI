// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that tracks slice length data across calls.
// The most interesting thing about this test is that S::new models the value of parameter s
// as a Reference to the parameter. When this gets back to the caller via the return result
// special handling is needed so that the caller does not end up with a reference to a reference.

use mirai_annotations::*;

struct S<'a> {
    slice: &'a [i64],
}

impl<'a> S<'a> {
    pub fn new(s: &'a [i64]) -> S<'a> {
        S { slice: s }
    }

    pub fn get_length(&self) -> usize {
        self.slice.len()
    }
}

pub fn main() {
    let a = [1; 100];
    let s = S::new(&a);
    let n = s.get_length();
    verify!(n == 100);
}
