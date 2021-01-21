// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test case that checks that effects that join old values with updates do not
// overwrite the caller's state when the joined value refines to the value that
// was there in the previous state.
// This matters when the target path is a slice, because the slice might alias
// another slice/index path and hence writing the pre-state value to the post-state
// (instead of just relying on it being there already) might overwrite a previous effect.

use mirai_annotations::*;

fn read_exact(a: &[u8], buf: &mut [u8]) {
    precondition!(buf.len() <= a.len());
    if buf.len() == 1 {
        buf[0] = a[0];
    } else {
        buf.copy_from_slice(a);
    }
}

pub fn t1(c: &[u8]) {
    precondition!(1 <= c.len());
    let mut buf = [0; 1];
    let _ = read_exact(c, &mut buf);
    verify!(buf[0] == 0); //~ possible false verification condition
}

pub fn main() {}
