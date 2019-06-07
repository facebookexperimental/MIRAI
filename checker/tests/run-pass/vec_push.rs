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
    let mut v: Vec<i32> = Vec::new();
    verify!(v.len() == 0);
    let old_len = v.len();
    v.push(0);
    verify!(v.len() == old_len + 1);
}

pub mod foreign_contracts {
    pub mod core {
        pub mod usize {
            pub const MAX: usize = 4294967295;
        }
    }

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
                    let old_len = self.len;
                    assume!(self.len == old_len);
                    self.len
                }

                pub fn push(&mut self, _value: T) {
                    precondition!(self.len < std::usize::MAX);
                    let old_len = self.len;
                    self.len += 1;
                    verify!(self.len == old_len + 1);
                }
            }
        }
    }
}
