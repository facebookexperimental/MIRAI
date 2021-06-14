// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Checks that argument types are tracked across return results

use mirai_annotations::*;

pub trait Tr {
    fn bar(&self) -> i32 {
        2
    }
}

struct Bar {
    i: i32,
}

impl Tr for Bar {
    fn bar(&self) -> i32 {
        self.i
    }
}

fn disguise(x: impl Tr) -> impl Tr {
    x
}

pub fn t1() {
    let b = Bar { i: 1 };
    let d = disguise(b);
    verify!(d.bar() == 1);
}

pub fn main() {}
