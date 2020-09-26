// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that u32::max_value and str::as_bytes(&self) are mangled correctly.

use mirai_annotations::*;

pub mod foreign_contracts {
    pub mod core {
        pub mod num {
            pub mod implement_u32 {
                pub fn max_value() -> u32 {
                    // deliberately wrong to ensure that the test will fail if
                    // u32::max_value() no longer compiles to this path.
                    2
                }
            }
        }

        pub mod str {
            pub mod implement_str {
                // not a real contract, just enough to validate path mangling
                pub fn as_bytes_(_self: &str) -> &[u8] {
                    &[1, 2, 3]
                }
            }
        }
    }
}

pub fn test1(size: u32) -> u32 {
    precondition!(size == u32::max_value());
    size
}

pub fn test2() {
    let b0 = "abc".as_bytes().len();
    verify!(b0 == 3);
}

pub fn main() {
    test1(2);
}
