// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test for adding and checking tags on empty structs

#![feature(const_generics)]
#![allow(incomplete_features)]

#[macro_use]
extern crate mirai_annotations;

pub mod propagation_on_empty_struct {
    use mirai_annotations::TagPropagationSet;

    struct SecretTaintKind<const MASK: TagPropagationSet> {}

    const SECRET_TAINT: TagPropagationSet = tag_propagation_set!();

    type SecretTaint = SecretTaintKind<SECRET_TAINT>;

    pub struct Foo { }

    pub fn test1() {
        let foo = Foo { };
        add_tag!(&foo, SecretTaint);
        verify!(has_tag!(&foo, SecretTaint));
    }

    pub fn test2() {
        let foo = Foo { };
        add_tag!(&foo, SecretTaint);
        call2(foo);
    }

    fn call2(foo: Foo) {
        // TODO: This should pass
        verify!(has_tag!(&foo, SecretTaint)); //~possible false verification condition
    }

    pub fn test3() {
        let foo = Foo { };
        add_tag!(&foo, SecretTaint);
        call3(foo); //~related location
    }

    fn call3(foo: Foo) {
        // TODO: This should pass
        precondition!(has_tag!(&foo, SecretTaint)); //~unsatisfied precondition
    }

    pub fn test4() {
        let foo = Foo { };
        add_tag!(&foo, SecretTaint);
        call4(&foo);
    }

    fn call4(foo: &Foo) {
        // TODO: This should pass
        verify!(has_tag!(foo, SecretTaint)); //~possible false verification condition
    }

    pub fn test5() {
        let foo = Foo { };
        add_tag!(&foo, SecretTaint);
        call5(&foo);
    }

    fn call5(foo: &Foo) {
        precondition!(has_tag!(foo, SecretTaint));
    }   
}

pub fn main() {}
