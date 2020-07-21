// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Tests for get_model_field!

#[macro_use]
extern crate mirai_annotations;

struct Foo {}

fn func(foo: &Foo) {
    precondition!(get_model_field!(foo, value, 0) == 99991);
}

pub fn main() {
    let foo = Foo {};
    set_model_field!(&foo, value, 99991);
    func(&foo);
    //todo: fix problem with refining post condition containing unknown model field
    verify!(get_model_field!(&foo, value, 0) == 99991); //~ this is unreachable, mark it as such by using the verify_unreachable! macro
}
