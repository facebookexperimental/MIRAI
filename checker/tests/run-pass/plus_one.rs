// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that array index assignments get weakened appropriately inside loop bodies

//todo: fix timeout
// use mirai_annotations::*;
//
// pub fn plus_one(key: [u8; 32]) {
//     let mut buf = key.to_vec();
//     for i in (0..32).rev() {
//         if buf[i] == 255 {
//             buf[i] = 0;
//             // If the above does a strong update on a widened i, then this branch will be
//             // unreachable in the next loop iteration and the diagnostic below will be suppressed.
//             bar(i); // ~ possible unsatisfied precondition
//         } else {
//             buf[i] = 1;
//         }
//     }
// }
//
// fn bar(i: usize) {
//     precondition!(i > 1); // ~ related location
// }

pub fn main() {}
