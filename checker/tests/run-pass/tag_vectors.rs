// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test for adding tags to vectors and vector elements

#![feature(const_generics)]
#![allow(incomplete_features)]

#[macro_use]
extern crate mirai_annotations;

pub mod propagation_for_vectors {
    use mirai_annotations::{TagPropagation, TagPropagationSet};

    struct SecretTaintKind<const MASK: TagPropagationSet> {}

    const SECRET_TAINT: TagPropagationSet = tag_propagation_set!(TagPropagation::SubComponent);

    type SecretTaint = SecretTaintKind<SECRET_TAINT>;

    pub struct Foo {
        content: i32,
    }

    pub fn test1() {
        let mut bar: Vec<Foo> = vec!();
        bar.push(Foo { content: 0 });
        add_tag!(&bar, SecretTaint);
        verify!(has_tag!(&bar, SecretTaint));
    }

    pub fn test2() {
        let mut bar: Vec<Foo> = vec!();
        bar.push(Foo { content: 0 });
        add_tag!(&bar[0], SecretTaint);
        verify!(has_tag!(&bar[0], SecretTaint));
    }

    pub fn test3() {
        let mut bar: Vec<Foo> = vec!();
        bar.push(Foo { content: 0 });
        add_tag!(&bar[0].content, SecretTaint);
        // TODO: This should pass
        verify!(has_tag!(&bar[0].content, SecretTaint)); //~possible false verification condition
    }

    pub fn test4() {
        let mut bar: Vec<Foo> = vec!();
        bar.push(Foo { content: 0 });
        add_tag!(&bar, SecretTaint);
        // TODO: TagPropagation::SubComponent should apply to vectors
        verify!(has_tag!(&bar[0], SecretTaint)); //~provably false verification condition
    }

    pub fn test5() {
        // Iteration should not affect tag propagation on vectors
        let mut bar: Vec<Foo> = vec!();
        bar.push(Foo { content: 0 });
        add_tag!(&bar, SecretTaint);
        for foo in bar.iter() {
            println!("{}", foo.content);
        }
        verify!(has_tag!(&bar, SecretTaint));
    }

    pub fn test6() {
        // Iteration should not affect tag propagation on vector elements
        let mut bar: Vec<Foo> = vec!();
        bar.push(Foo { content: 0 });
        add_tag!(&bar[0], SecretTaint);
        for foo in bar.iter() {
            println!("{}", foo.content);
        }
        verify!(has_tag!(&bar[0], SecretTaint));
    }

    pub fn test7() {
        let mut bar: Vec<Foo> = vec!();
        bar.push(Foo { content: 0 });
        for foo in bar.iter() {
            add_tag!(foo, SecretTaint);
            println!("{}", foo.content);
        }
        // TODO: It should be possible to add tags during iteration
        verify!(has_tag!(&bar[0], SecretTaint)); //~provably false verification condition
    }

    pub fn test8() {
        let mut bar: Vec<Foo> = vec!();
        bar.push(Foo { content: 0 });
        for foo in bar.iter() {
            add_tag!(foo, SecretTaint);
            println!("{}", foo.content);
        }
        // TODO: It should be possible to check tags during iteration
        for foo in bar.iter() {
            verify!(has_tag!(foo, SecretTaint)); //~this is unreachable, mark it as such by using the verify_unreachable! macro
            println!("{}", foo.content);
        }
    }
}

pub fn main() {}
