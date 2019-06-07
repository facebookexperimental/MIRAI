// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that exercises visit_used_move with a structured value.

#![feature(type_alias_enum_variants)]

#[macro_use]
extern crate mirai_annotations;

pub fn main() {
    let v: Vec<i32> = Vec::new();
    verify!(v.len() == 0);
}

pub mod foreign_contracts {
    pub mod alloc {
        pub mod vec {
            pub struct Vec<T> {
                _phantom: std::marker::PhantomData<T>,
                pub len: usize,
            }
            
            impl<T> Vec<T> {
                pub fn new() -> Vec<T> {
                    Vec {
                        _phantom: std::marker::PhantomData,
                        len: 0,
                    }
                }

                pub fn len(&self) -> usize {
                    self.len
                }
            }
        }
    }
}
