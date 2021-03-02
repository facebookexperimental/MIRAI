// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that first assumes something that is unprovable and then relies on it to "prove" a verify condition

use mirai_annotations::*;

pub fn t1() {
    foo1(2); // This breaks an assumed pre-condition and leads to a runtime failure.
             // It is not checked by Mirai, because of the assumption.
             // Unlike this test case, in real life assumptions are made for complicated reasons that are
             // hard to encode in checked preconditions.
}

pub fn foo1(i: i32) {
    checked_assume!(i == 3); // this is a pre-condition that is assumed to hold at call sites.
                             // It is not promoted, but it is checked here at runtime.
    let x = if i == 3 { 1 } else { 2 };
    verify!(x == 1); // This is neither true, nor checked at runtime, but it can only fail if
                     // the assumption above, which is checked at runtime, does not fail.
}

pub fn t2() {
    foo2(2); //~ assertion failed
             // This gives a diagnostic because foo2 asserts i == 3 which gets promoted to a precondition
}

fn foo2(i: i32) {
    // this becomes an inferred precondition
    assert_eq!(i, 3); //~ related location
    let x = if i == 3 { 1 } else { 2 };
    verify!(x == 1); // This is neither true, nor checked at runtime, but it can only fail if
                     // the assert_eq fails, so the problem is already pointed out and we need not repeat ourselves.
}

pub fn main() {}
