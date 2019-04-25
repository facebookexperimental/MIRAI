// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a contract defined locally for an imported (core) function.
#![feature(type_alias_enum_variants)]

#[macro_use]
extern crate mirai_annotations;

pub mod foreign_contracts {
    pub mod core {
        pub mod option {
            pub enum Option<T> {
                None,
                Some(T),
            }

            impl<T> Option<T> {
                pub fn unwrap(self) -> T {
                    precondition!(
                        match self {
                            Self::None => false,
                            _ => true,
                        },
                        "self may not be None"
                    );
                    assume!(false);
                    unreachable!();
                }
            }
        }
    }
}

pub fn main() {
    let x: Option<i64> = Some(1);
    let _y = x.unwrap();
    let z: Option<i64> = None;
    let _ = z.unwrap(); //~ unsatisfied precondition: self may not be None
}
