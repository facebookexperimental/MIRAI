// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that assigns to a location that is unknown at compile time.
#![feature(box_syntax)]

#[macro_use]
extern crate mirai_annotations;

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
        verify!(c.f == 3);
    }
//    todo: enable the next two asserts when the fixed point logic gets better
//    (if there are two asserts the second shares the unwind block of the first and does
//    a backwards branch to it, leading to a fixed point loop that widens and thus loses
//    precision).
//    verify!(a.f == if cond { 3 } else { 1 });
//    verify!(b.f == if cond { 2 } else { 3 });
//    todo: #32 enable this when the simplifier gets better
//    verify!(if cond { a.f == 3 } else { b.f == 3 });
//    verify!(if !cond { a.f == 1 } else { b.f == 2 });
}
