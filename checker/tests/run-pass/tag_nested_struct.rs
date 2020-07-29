// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test for adding and checking tags on nested structs

#![feature(const_generics)]
#![allow(incomplete_features)]

#[macro_use]
extern crate mirai_annotations;

use mirai_annotations::{TagPropagation, TagPropagationSet};

struct SecretTaintKind<const MASK: TagPropagationSet> {}

const SECRET_TAINT: TagPropagationSet = tag_propagation_set!(TagPropagation::SubComponent);

type SecretTaint = SecretTaintKind<SECRET_TAINT>;

struct SecretSanitizerKind<const MASK: TagPropagationSet> {}

const SECRET_SANITIZER: TagPropagationSet = tag_propagation_set!(TagPropagation::SubComponent);

type SecretSanitizer = SecretSanitizerKind<SECRET_SANITIZER>;

pub struct Foo {
    bar: Bar,
}

pub struct Bar {
    content: i32,
}

pub fn test1() {
    let foo = Foo {
        bar: Bar { content: 99991 },
    };
    add_tag!(&foo, SecretTaint);
    verify!(has_tag!(&foo, SecretTaint));
    verify!(has_tag!(&foo.bar.content, SecretTaint));
    verify!(has_tag!(&foo.bar, SecretTaint));
}

pub fn test2() {
    let foo = Foo {
        bar: Bar { content: 99991 },
    };
    add_tag!(&foo.bar, SecretTaint);
    add_tag!(&foo, SecretSanitizer);
    verify!(has_tag!(&foo.bar, SecretTaint));
    verify!(has_tag!(&foo.bar, SecretSanitizer));
    verify!(does_not_have_tag!(&foo, SecretTaint));
    verify!(has_tag!(&foo, SecretSanitizer));
}

pub fn test3(foo: Foo) {
    add_tag!(&foo, SecretTaint);
    verify!(has_tag!(&foo, SecretTaint));
    // todo: deal with unknown paths rooted at parameters
    verify!(has_tag!(&foo.bar.content, SecretTaint)); //~ possible false verification condition
    verify!(has_tag!(&foo.bar, SecretTaint)); //~ possible false verification condition
}

pub fn main() {}
