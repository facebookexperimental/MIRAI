// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that calls std::intrinsics::unreachable conditionally.

#![allow(internal_features)]
#![feature(core_intrinsics)]
#![allow(unused)]

use std::intrinsics;

pub fn foo(flag: bool) {
    if flag {
        unsafe {
            intrinsics::unreachable();
        }
    }
}
