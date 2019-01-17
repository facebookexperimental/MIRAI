// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses paths containing base addresses.

#![feature(box_syntax)]
pub struct Foo { pub x: i32, pub y: i64 }
pub fn f() -> Box<Foo> {
    let foo = Foo { x: 1, y: 1111111111111111111 };
    box foo
}
