// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test for adding and checking tags on empty structs

#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

#[macro_use]
extern crate mirai_annotations;

pub mod propagation_on_empty_struct {
    use mirai_annotations::TagPropagationSet;

    struct SecretTaintKind<const MASK: TagPropagationSet> {}

    const SECRET_TAINT: TagPropagationSet = tag_propagation_set!();

    type SecretTaint = SecretTaintKind<SECRET_TAINT>;

    pub struct Foo {}

    pub fn test1() {
        let foo = Foo {};
        add_tag!(&foo, SecretTaint);
        verify!(has_tag!(&foo, SecretTaint));
    }

    pub fn test2() {
        let foo = Foo {};
        add_tag!(&foo, SecretTaint);
        call2(foo);
    }

    fn call2(foo: Foo) {
        // Cannot verify this without a precondition
        verify!(has_tag!(&foo, SecretTaint)); //~possible false verification condition
    }

    pub fn test3() {
        let foo = Foo {};
        add_tag!(&foo, SecretTaint);
        // Sadly, the next call is compiled by Rust with an argument that constructs a new empty struct.
        // Thus the tag added above is not present on the actual argument and the precondition fails.
        call3(foo); //~unsatisfied precondition
    }

    pub fn test3_constant() {
        const FOO: Foo = Foo {};
        add_tag!(&FOO, SecretTaint);
        // Sadly, the next call is compiled by Rust with an argument that constructs a new empty struct.
        // Thus the tag added above is not present on the actual argument and the precondition fails.
        call3(FOO); //~unsatisfied precondition
    }

    fn call3(foo: Foo) {
        precondition!(has_tag!(&foo, SecretTaint)); //~related location
                                                    //~related location
    }

    pub fn test4() {
        let foo = Foo {};
        add_tag!(&foo, SecretTaint);
        call4(&foo);
    }

    fn call4(foo: &Foo) {
        // Cannot verify this without a precondition
        verify!(has_tag!(foo, SecretTaint)); //~possible false verification condition
    }

    pub fn test5() {
        let foo = Foo {};
        add_tag!(&foo, SecretTaint);
        call5(&foo);
    }

    fn call5(foo: &Foo) {
        precondition!(has_tag!(foo, SecretTaint));
    }
}

pub fn main() {}
