// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that std::u64::MAX is set correctly
#![allow(non_snake_case)]

#[macro_use]
extern crate mirai_annotations;

pub fn main() {
    verify!(std::u64::MAX == 9223372036854775807);
}

pub mod foreign_contracts {
    pub mod core {
        pub mod u64 {
            pub const MAX: u64 = 9223372036854775807;
        }
    }
}
