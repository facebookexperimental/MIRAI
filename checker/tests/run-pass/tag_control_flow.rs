// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test for tag propagation through control flows

#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

use mirai_annotations::*;

struct SecretTaintKind<const MASK: TagPropagationSet> {}

const SECRET_TAINT: TagPropagationSet = tag_propagation_set!(TagPropagation::BitOr);

type SecretTaint = SecretTaintKind<SECRET_TAINT>;

pub fn test1(cond: bool) {
    let secret = 23333;
    if cond {
        add_tag!(&secret, SecretTaint);
        verify!(has_tag!(&secret, SecretTaint));
    }
    verify!(has_tag!(&secret, SecretTaint)); //~ possible false verification condition
}

pub fn test2(cond: bool) {
    let secret = 23333;
    while cond {
        add_tag!(&secret, SecretTaint);
        verify!(has_tag!(&secret, SecretTaint));
    }
    verify!(has_tag!(&secret, SecretTaint)); //~ possible false verification condition
}

pub fn test3(cond: bool) {
    let secret = 23333;
    loop {
        add_tag!(&secret, SecretTaint);
        verify!(has_tag!(&secret, SecretTaint));
        if !cond {
            break;
        }
    }
    verify!(has_tag!(&secret, SecretTaint));
}

pub fn main() {}
