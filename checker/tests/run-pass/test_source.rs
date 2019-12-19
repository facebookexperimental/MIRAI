// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

#[macro_use]
extern crate mirai_annotations;

// MIRAI_FLAGS --test_only --diag=strict

#[test]
fn some_test() {
    verify!(1 == 1);
}

#[test]
fn another_test() {
    verify!(2 == 1); //~provably false verification condition
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

    // With --diag=strict we still see an error even though d.f is uninterpreted.
    verify!(d.f(1) == 3); //~ possible false verification condition
    verify!(3 == 4); //~provably false verification condition
}

pub fn not_a_test() {
    // Should not complain because it is not a test function.
    verify!(2 == 1);
}
