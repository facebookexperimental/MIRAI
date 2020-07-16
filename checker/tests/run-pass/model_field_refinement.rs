// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test where function preconditions involve model/tag fields of parameters
// todo: deal with refinement of unknown model/tag fields (issue #577)

#![feature(const_generics)]
#![allow(incomplete_features)]

#[macro_use]
extern crate mirai_annotations;

use mirai_annotations::TagPropagationSet;

struct Foo {}

fn func1(foo: &Foo) {
    precondition!(get_model_field!(foo, value, 0) == 99991);
}

pub fn test1() {
    let foo = Foo {};
    set_model_field!(&foo, value, 99991);
    func1(&foo);
    verify!(get_model_field!(&foo, value, 0) == 99991); //~ this is unreachable, mark it as such by using the verify_unreachable! macro
}

struct TaintKind<const MASK: TagPropagationSet> {}

const TAINT: TagPropagationSet = tag_propagation_set!();

type Taint = TaintKind<TAINT>;

fn func2(foo: &Foo) {
    precondition!(has_tag!(foo, Taint));
}

pub fn test2() {
    let foo = Foo {};
    add_tag!(&foo, Taint);
    func2(&foo);
    verify!(has_tag!(&foo, Taint)); //~ this is unreachable, mark it as such by using the verify_unreachable! macro
}

pub fn main() {}
