// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that size_of::<u32>() is mangled correctly.
#![allow(non_snake_case)]

use mirai_annotations::*;
use std::mem::size_of;

pub fn main() {
    verify!(size_of::<u32>() == 4);
}

pub mod foreign_contracts {
    pub mod core {
        pub mod mem {
            pub fn size_of__u32() -> usize {
                4
            }
        }
    }
}
