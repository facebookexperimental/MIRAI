// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

use mirai_annotations::*;

// MIRAI_FLAGS --test_only --diag=verify

#[test]
fn some_test() {
    verify!(1 == 1);
}

#[test]
fn another_test() {
    verify!(2 == 1); //~ provably false verification condition
}

#[test]
fn no_summary_analyzed_anyway() {
    trait Dynamic {
        fn f(&self, x: u64) -> u64;
    }
    struct S;
    impl Dynamic for S {
        fn f(&self, x: u64) -> u64 {
            return x + 1;
        }
    }
    let d: &dyn Dynamic = &S {} as &dyn Dynamic; // forget type info of S

    let i = d.f(1); //~ the called function could not be summarized
    verify!(i == 3); // ignored because the previous unresolved call makes every subsequent thing moot
}

pub fn main() {
    // Should not complain because it is not a test function and therefore not analyzed.
    verify!(2 == 1);
}
