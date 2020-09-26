// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that assigns to a location that is unknown at compile time.

use mirai_annotations::*;

pub fn main() {
    do_join(true);
}

fn do_join(cond: bool) {
    let mut a = [1];
    let mut b = [2];
    {
        let mut c = if cond { &mut a } else { &mut b };
        (&mut c)[0] = 3;
        verify!(c[0] == 3);
    }
    verify!(a[0] == if cond { 3 } else { 1 });
    verify!(b[0] == if cond { 2 } else { 3 });
    verify!(if cond { a[0] == 3 } else { b[0] == 3 });
    verify!(if !cond { a[0] == 1 } else { b[0] == 2 });
}
