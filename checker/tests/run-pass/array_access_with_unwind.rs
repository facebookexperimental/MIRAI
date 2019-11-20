// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that needs to do cleanup if an array access is out of bounds.

#![allow(non_snake_case)]

#[macro_use]
extern crate mirai_annotations;

pub mod foreign_contracts {
    pub mod core {
        pub mod iter {
            pub mod traits {
                pub mod iterator {
                    pub mod Iterator {
                        pub fn next<T>() -> T {
                            result!()
                        }
                    }
                }
            }
        }
        pub mod slice {
            pub mod SliceIndex {
                pub fn get_unchecked_mut<T>() -> T {
                    result!()
                }
            }
        }
    }
}

pub fn foo(arr: &mut [i32], i: usize) -> String {
    arr[i] = 123; //~ possible index out of bounds
    let result = String::from("foo"); // allocate something that needs explicit cleanup
    let _e = arr[i]; // no warning here because we can't get here unless the assignment succeeded
    result
}

pub fn main() {}
