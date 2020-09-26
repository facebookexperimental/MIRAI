// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that constrains an unknown model field and then relies on the constraint.

use mirai_annotations::*;

pub trait Foo {
    fn bar(&mut self) {
        precondition!(get_model_field!(&self, f, 0) < 1000);
        set_model_field!(&self, f, get_model_field!(&self, f, 0) + 1);
    }
}

pub fn main() {}
