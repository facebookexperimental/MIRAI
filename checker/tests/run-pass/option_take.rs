// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

use mirai_annotations::*;

fn take_out(menu: &mut Option<i32>) -> i32 {
    menu.take().unwrap()
}

pub fn t1() {
    let mut some_one = Some(1);
    let i = take_out(&mut some_one);
    verify!(i == 1);
    verify!(some_one.is_none());
}

pub fn main() {}
