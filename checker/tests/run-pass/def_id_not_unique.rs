// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that call two distinct instantiations of the same generic functions in such a way
// that both calls will use the same DefId, with the result that the second call will use
// the wrong summary if using a cache that is keyed by DefId.

// This example is highly contrived, but inspired by a larger way more subtle code fragment.

#![allow(non_snake_case)]

use mirai_annotations::*;

pub mod foreign_contracts {
    pub mod def_id_not_unique {
        pub trait Foo {
            fn one__T_i32(&self, _t: i32) -> i32 {
                2
            }

            fn one__T_i64(_t: i64) -> i64 {
                3
            }
        }
    }
}

pub fn foo<T: Foo>(bar: &T) {
    let i: i32 = 0;
    verify!(bar.one(i) == 2);
    let d: i64 = 0;
    verify!(bar.one(d) == 3);
}

pub trait Foo {
    fn one<T>(&self, t: T) -> T;
}

pub fn main() {}
