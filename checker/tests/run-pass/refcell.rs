// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

//todo: fix this

// use std::cell::RefCell;
//
// struct MutableOnTheInside {
//     f: RefCell<u64>,
// }
//
// pub fn t1() {
//     let s = MutableOnTheInside { f: RefCell::new(0) };
//     foo(&s, &s); // ~ possible result unwrap failed
// }
//
// // if s1 and s2 alias, there will be two writes to the same memory via distinct access paths
// // s1.f and s2.f
// fn foo(s1: &MutableOnTheInside, s2: &MutableOnTheInside) {
//     let mut bor = s1.f.borrow_mut();
//     *s2.f.borrow_mut() = 2; // ~ related location
//     *bor = 3; // ~ related location
// } // ~ related location

pub fn main() {}
