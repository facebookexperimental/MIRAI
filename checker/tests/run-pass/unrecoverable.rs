// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that calls calls unrecoverable! and panic! in way that demonstrates their respective use cases.

use mirai_annotations::*;

pub fn test1() {
    unrecoverable!("Something happened for which the correct response is termination");
}

pub fn test2(message: &str) {
    unrecoverable!("this happened {}", message);
}

pub fn test3() {
    panic!("Whoa execution should never get here, bug bug bug!"); //~ Whoa execution should never get here, bug bug bug!
}

pub fn main() {}
