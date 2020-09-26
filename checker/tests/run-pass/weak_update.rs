// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that does a weak update of an array element

use mirai_annotations::*;

pub fn test1(i: usize) {
    precondition!(i < 3);
    let mut a = [3, 4, 5];
    a[i] = 666;
    verify!(a[i] == 666);
    verify!(a[0] == 3 || a[0] == 666);
    if i != 0 {
        verify!(a[0] == 3);
    } else {
        verify!(a[0] == 3); //~ provably false verification condition
    }
}

pub struct Foo {
    pub bar: u32,
    pub bas: i32,
}

pub fn test2(i: usize) {
    precondition!(i < 3);
    let mut a = [
        Foo { bar: 3, bas: -3 },
        Foo { bar: 4, bas: -4 },
        Foo { bar: 5, bas: -5 },
    ];
    a[i] = Foo {
        bar: 666,
        bas: -666,
    };
    verify!(a[i].bar == 666);
    verify!(a[i].bas == -666);
    verify!(a[0].bar == 3 || a[0].bar == 666);
    verify!(a[0].bas == -3 || a[0].bas == -666);
    if i != 0 {
        verify!(a[0].bar == 3);
        verify!(a[0].bas == -3);
    } else {
        verify!(a[0].bar == 3); //~ provably false verification condition
    }
}

pub fn main() {}
