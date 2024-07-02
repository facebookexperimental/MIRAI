// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that calls Option::and_then

// use mirai_annotations::*;
//
// fn sq(x: u32) -> Option<u32> {
//     Some(x * x)
// }
// fn nope(_: u32) -> Option<u32> {
//     None
// }

pub fn main() {
    // verify!(Some(2).and_then(sq).unwrap() == 4);
    // verify!(Some(2).and_then(sq).and_then(sq).unwrap() == 16);
    // verify!(Some(2).and_then(sq).and_then(nope).is_none());
    // verify!(Some(2).and_then(nope).and_then(sq).is_none());
    // verify!(None.and_then(sq).and_then(sq).is_none());
    // Some(1).and_then(must_be_one);
    // Some(2).and_then(must_be_one); // ~ unsatisfied precondition
}

// fn must_be_one(x: u32) -> Option<u32> {
//     precondition!(x == 1); // ~ related location
//     None // ~ related location
// }
