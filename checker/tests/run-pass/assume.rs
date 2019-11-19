// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that first assumes something that is unprovable and then relies on it to "prove" a verify condition

#[macro_use]
extern crate mirai_annotations;

pub fn main() {
    foo(2); // This breaks an assumed pre-condition and leads to a runtime failure.
            // It is not checked by Mirai, because of the assumption.
            // Unlike this test case, in real life assumptions are made for complicated reasons that are
            // hard to encode in checked preconditions.
    foo2(2); // The inferred precondition that i == 3 is upheld here because foo assumed that i == 3
             // and this assumption leaks to the call site via the inferred post condition.
             // I.e. we assumed that 2 == 3 and we are paying the price for that.
}

pub fn foo(i: i32) {
    checked_assume!(i == 3); // this is a pre-condition that is assumed to hold.
                             // It is not promoted, but it is checked here at runtime.
    let x = if i == 3 { 1 } else { 2 };
    verify!(x == 1); // This is neither true, nor checked at runtime, but it can only fail if
                     // the assumption above, which is checked at runtime, does not fail.
}

fn foo2(i: i32) {
    verify!(i == 3); // this becomes an inferred precondition
    let x = if i == 3 { 1 } else { 2 };
    verify!(x == 1); // This is neither true, nor checked at runtime, but it can only fail if
                     // the first verify fails, so the problem is already pointed out and we need not repeat ourselves.
}
