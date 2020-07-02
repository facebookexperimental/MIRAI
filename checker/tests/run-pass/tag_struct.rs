// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test for adding tags to structs and checking tags on fields

#![feature(const_generics)]
#![allow(incomplete_features)]

#[macro_use]
extern crate mirai_annotations;

use mirai_annotations::{TagPropagation, TagPropagationSet};

struct SecretTaintKind<const MASK: TagPropagationSet> {}

const SECRET_TAINT: TagPropagationSet = tag_propagation_set!(TagPropagation::BitOr);

type SecretTaint = SecretTaintKind<SECRET_TAINT>;

pub struct Foo {
    content: i32,
}

pub fn test1() {
    let foo = Foo { content: 99991 };
    add_tag!(&foo, SecretTaint);
    verify!(has_tag!(&foo.content, SecretTaint));
}

pub fn test2(cond: bool) {
    let left = Foo { content: 12345 };
    let right = Foo { content: 54321 };
    let join;
    if cond {
        join = &left;
    } else {
        join = &right;
    }
    add_tag!(&join.content, SecretTaint);
    verify!(has_tag!(&left.content, SecretTaint) || has_tag!(&right.content, SecretTaint));
}

pub fn test3(cond: bool) {
    let left = Foo { content: 12345 };
    let right = Foo { content: 54321 };
    let join;
    if cond {
        join = &left;
    } else {
        join = &right;
    }
    add_tag!(join, SecretTaint);
    verify!(has_tag!(&left.content, SecretTaint) || has_tag!(&right.content, SecretTaint));
}

pub fn test4(foo: Foo, cond: bool) {
    let bar = Foo { content: 99991 };
    let join;
    if cond {
        join = &foo;
    } else {
        join = &bar;
    }
    add_tag!(&join.content, SecretTaint);
    verify!(has_tag!(&foo.content, SecretTaint) || has_tag!(&bar.content, SecretTaint));
}

pub fn test5(foo: Foo, cond: bool) {
    let bar = Foo { content: 99991 };
    let join;
    if cond {
        join = &foo;
    } else {
        join = &bar;
    }
    add_tag!(join, SecretTaint);
    // todo: deal with unknown paths rooted at parameters
    verify!(has_tag!(&foo.content, SecretTaint) || has_tag!(&bar.content, SecretTaint));
    //~ possible false verification condition
}

pub fn main() {}
