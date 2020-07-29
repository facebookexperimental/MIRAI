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
    verify!(has_tag!(&foo.bar.content, SecretTaint));
    verify!(has_tag!(&foo.bar, SecretTaint));
}

pub fn test4(foo: Foo) {
    add_tag!(&foo.bar, SecretTaint);
    add_tag!(&foo, SecretSanitizer);
    verify!(has_tag!(&foo.bar, SecretTaint));
    verify!(has_tag!(&foo.bar, SecretSanitizer));
    verify!(has_tag!(&foo, SecretSanitizer));
    verify!(does_not_have_tag!(&foo, SecretTaint)); //~ possible false verification condition
}

pub fn test5(foo: &Foo) {
    add_tag!(foo, SecretTaint);
    verify!(has_tag!(foo, SecretTaint));
    verify!(has_tag!(&foo.bar.content, SecretTaint));
    verify!(has_tag!(&foo.bar, SecretTaint));
}

pub fn test6(foo: &Foo) {
    add_tag!(&foo.bar, SecretTaint);
    add_tag!(foo, SecretSanitizer);
    verify!(has_tag!(&foo.bar, SecretTaint));
    verify!(has_tag!(&foo.bar, SecretSanitizer));
    verify!(has_tag!(foo, SecretSanitizer));
    verify!(does_not_have_tag!(foo, SecretTaint)); //~ possible false verification condition
}

fn taint_argument_for_test7(foo: &Foo) {
    add_tag!(foo, SecretTaint);
}

pub fn test7() {
    let foo = Foo {
        bar: Bar { content: 99991 },
    };
    taint_argument_for_test7(&foo);
    verify!(has_tag!(&foo, SecretTaint));
    // todo: propagate tags during refinements
    verify!(has_tag!(&foo.bar.content, SecretTaint)); //~ provably false verification condition
    verify!(has_tag!(&foo.bar, SecretTaint)); //~ this is unreachable, mark it as such by using the verify_unreachable! macro
}

fn taint_argument_for_test8(foo: &Foo) {
    add_tag!(foo, SecretTaint);
    add_tag!(&foo.bar, SecretSanitizer);
}

pub fn test8() {
    let foo = Foo {
        bar: Bar { content: 99991 },
    };
    taint_argument_for_test8(&foo);
    // todo: propagate tags during refinements
    verify!(has_tag!(&foo.bar, SecretTaint)); //~ provably false verification condition
    verify!(has_tag!(&foo.bar, SecretSanitizer)); //~ this is unreachable, mark it as such by using the verify_unreachable! macro
    verify!(does_not_have_tag!(&foo, SecretTaint)); //~ this is unreachable, mark it as such by using the verify_unreachable! macro
    verify!(has_tag!(&foo, SecretSanitizer)); //~ this is unreachable, mark it as such by using the verify_unreachable! macro
}

pub fn main() {}
