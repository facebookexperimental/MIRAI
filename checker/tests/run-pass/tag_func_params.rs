// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test for tag tracking involving function calls

#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

use mirai_annotations::*;

struct SecretTaintKind<const MASK: TagPropagationSet> {}

const SECRET_TAINT: TagPropagationSet = tag_propagation_set!(TagPropagation::SubComponent);

type SecretTaint = SecretTaintKind<SECRET_TAINT>;

fn argument_must_be_tainted_val(value: i32) {
    precondition!(has_tag!(&value, SecretTaint));
}

fn argument_must_be_tainted_ref(value: &i32) {
    precondition!(has_tag!(value, SecretTaint));
}

pub fn test1() {
    let secret = 99991;
    add_tag!(&secret, SecretTaint);
    argument_must_be_tainted_val(secret);
    argument_must_be_tainted_ref(&secret);
}

fn taint_argument_val(value: i32) {
    add_tag!(&value, SecretTaint);
}

fn taint_argument_ref(value: &i32) {
    add_tag!(value, SecretTaint);
}

pub fn test2() {
    let secret = 99991;
    taint_argument_val(secret);
    verify!(does_not_have_tag!(&secret, SecretTaint));
    taint_argument_ref(&secret);
    verify!(has_tag!(&secret, SecretTaint));
}

struct Foo {
    content: i32,
}

fn struct_argument_must_be_tainted_val(foo: Foo) {
    precondition!(has_tag!(&foo, SecretTaint));
    precondition!(has_tag!(&foo.content, SecretTaint));
}

pub fn test3() {
    let foo = Foo { content: 99991 };
    add_tag!(&foo, SecretTaint);
    struct_argument_must_be_tainted_val(foo);
}

fn struct_argument_must_be_tainted_ref(foo: &Foo) {
    precondition!(has_tag!(foo, SecretTaint));
    precondition!(has_tag!(&foo.content, SecretTaint));
}

pub fn test4() {
    let foo = Foo { content: 99991 };
    add_tag!(&foo, SecretTaint);
    struct_argument_must_be_tainted_ref(&foo);
}

pub fn main() {}
