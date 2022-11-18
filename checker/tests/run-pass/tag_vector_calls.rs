// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test for adding tags to vectors and checking the tags in calls

#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

#[macro_use]
extern crate mirai_annotations;

pub mod propagation_for_vector_calls {
    use mirai_annotations::{TagPropagation, TagPropagationSet};

    struct SecretTaintKind<const MASK: TagPropagationSet> {}

    const SECRET_TAINT: TagPropagationSet = tag_propagation_set!(TagPropagation::SubComponent);

    type SecretTaint = SecretTaintKind<SECRET_TAINT>;

    pub struct Foo {
        content: i32,
    }

    pub fn test1() {
        let mut bar: Vec<Foo> = vec![];
        bar.push(Foo { content: 0 });
        add_tag!(&bar, SecretTaint);
        call1(bar);
    }

    fn call1(bar: Vec<Foo>) {
        // A failed verify! does not promote to a precondition.
        verify!(has_tag!(&bar, SecretTaint)); //~possible false verification condition
    }

    pub fn test2() {
        let mut bar: Vec<Foo> = vec![];
        bar.push(Foo { content: 0 });
        add_tag!(&bar, SecretTaint);
        call2(bar);
    }

    fn call2(bar: Vec<Foo>) {
        precondition!(has_tag!(&bar, SecretTaint));
    }

    pub fn test3() {
        let mut bar: Vec<Foo> = vec![];
        bar.push(Foo { content: 0 });
        add_tag!(&bar[0], SecretTaint);
        call3(bar);
    }

    fn call3(bar: Vec<Foo>) {
        // A failed verify! does not promote to a precondition.
        verify!(has_tag!(&bar[0], SecretTaint)); //~possible false verification condition
    }

    pub fn test4() {
        let mut bar: Vec<Foo> = vec![];
        bar.push(Foo { content: 0 });
        add_tag!(&bar[0], SecretTaint);
        // todo: fix this
        // call4(bar);
    }

    // fn call4(bar: Vec<Foo>) {
    //     precondition!(has_tag!(&bar[0], SecretTaint));
    // }

    pub fn test5() {
        let mut bar: Vec<Foo> = vec![];
        bar.push(Foo { content: 0 });
        add_tag!(&bar[0].content, SecretTaint);
        call5(bar);
    }

    fn call5(bar: Vec<Foo>) {
        // A failed verify! does not promote to a precondition.
        verify!(has_tag!(&bar[0].content, SecretTaint)); //~possible false verification condition
    }

    pub fn test6() {
        let mut bar: Vec<Foo> = vec![];
        bar.push(Foo { content: 0 });
        add_tag!(&bar[0].content, SecretTaint);
        //todo: fix this
        // call6(bar); // ~ possible unsatisfied precondition
    }

    // fn call6(bar: Vec<Foo>) {
    //     precondition!(has_tag!(&bar[0].content, SecretTaint)); // ~ related location
    // }

    pub fn test7() {
        let mut bar: Vec<Foo> = vec![];
        bar.push(Foo { content: 0 });
        add_tag!(&bar, SecretTaint);
        call7(bar);
    }

    fn call7(bar: Vec<Foo>) {
        // A failed verify! does not promote to a precondition.
        verify!(has_tag!(&bar[0], SecretTaint)); //~possible false verification condition
    }

    pub fn test8() {
        let mut bar: Vec<Foo> = vec![];
        bar.push(Foo { content: 0 });
        add_tag!(&bar, SecretTaint);
        call8(bar);
    }

    fn call8(bar: Vec<Foo>) {
        precondition!(has_tag!(&bar[0], SecretTaint));
    }

    pub fn test9() {
        let mut bar: Vec<Foo> = vec![];
        bar.push(Foo { content: 0 });
        add_tag!(&bar, SecretTaint);
        call9(bar);
    }

    fn call9(bar: Vec<Foo>) {
        // A failed verify! does not promote to a precondition.
        verify!(has_tag!(&bar[0].content, SecretTaint)); //~possible false verification condition
    }

    pub fn test10() {
        let mut bar: Vec<Foo> = vec![];
        bar.push(Foo { content: 0 });
        add_tag!(&bar, SecretTaint);
        call10(bar);
    }

    fn call10(bar: Vec<Foo>) {
        precondition!(has_tag!(&bar[0].content, SecretTaint));
    }
}

pub fn main() {}
