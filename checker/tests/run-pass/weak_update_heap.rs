// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that assigns to a location that is unknown at compile time.
#![feature(box_syntax)]

// use mirai_annotations::*;

pub fn main() {
    do_join(true);
}

struct Foo {
    f: i32,
}

fn do_join(cond: bool) {
    let mut a = box Foo { f: 1 };
    let mut b = box Foo { f: 2 };
    {
        let c = if cond { &mut a } else { &mut b };
        c.f = 3;
        // verify!(c.f == 3);
    }
    // verify!(a.f == if cond { 3 } else { 1 });
    // verify!(b.f == if cond { 2 } else { 3 });
    // verify!(if cond { a.f == 3 } else { b.f == 3 });
    //todo: fix this
    // verify!(if !cond { a.f == 1 } else { b.f == 2 });
}
