// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Check that self recursive calls happening via trait methods are detected.

use mirai_annotations::*;

pub trait X {
    fn foo() -> usize;
}

pub struct Y<U> {
    pub a: U,
}

impl<U: X> X for Y<U> {
    fn foo() -> usize {
        U::foo() + 1
    }
}

pub struct Z {
    pub b: u8,
}

impl X for Z {
    fn foo() -> usize {
        1
    }
}

pub fn main() {
    verify!(Z::foo() == 1);
    verify!(Y::<Z>::foo() == 2);
    verify!(Y::<Y<Z>>::foo() == 3);
    verify!(Y::<Y<Y<Z>>>::foo() == 4);
    verify!(Y::<Y<Y<Y<Z>>>>::foo() == 5);
    verify!(Y::<Y<Y<Y<Y<Z>>>>>::foo() == 6);
}
