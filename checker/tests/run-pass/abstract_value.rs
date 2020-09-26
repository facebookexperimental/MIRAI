// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses abstract_value!

use mirai_annotations::*;

pub fn main() {
    let a = abstract_value!(6i32);
    let b = abstract_value!(7i32);
    assume!(4 < a && a < 8); // a in [5,7]
    assume!(5 < b && b < 9); // b in [6,8]
    verify!(30 <= a * b && a * b <= 56); // a*b in [30,56]
}
