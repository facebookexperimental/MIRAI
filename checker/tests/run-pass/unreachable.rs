// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that calls std::intrinsics::unreachable unconditionally.

#![feature(core_intrinsics)]
#![allow(unused)]

#[macro_use]
extern crate mirai_annotations;

use std::intrinsics;

fn foo() {
    unsafe {
        intrinsics::unreachable();
    }
}
