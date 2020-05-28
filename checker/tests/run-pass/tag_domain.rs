// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test for basic tracking of tags

#![feature(const_generics)]
#![allow(incomplete_features)]

#[macro_use]
extern crate mirai_annotations;

use mirai_annotations::{TagPropagation, TagPropagationSet};

struct SecretTaint<const MASK: TagPropagationSet> {}

const SECRET_TAINT: TagPropagationSet =
    tag_propagation_set!(TagPropagation::Add, TagPropagation::Xor);

struct SecretSanitizer<const MASK: TagPropagationSet> {}

const SECRET_SANITIZER: TagPropagationSet = tag_propagation_set!();

pub fn main() {
    let secret = 23333;
    add_tag!(&secret, SecretTaint<SECRET_TAINT>);
    verify!(has_tag!(&secret, SecretTaint<SECRET_TAINT>));
    verify!(does_not_have_tag!(
        &secret,
        SecretSanitizer<SECRET_SANITIZER>
    ));
    let info = secret + 1;
    // verify!(has_tag!(&info, SecretTaint<SECRET_TAINT>));
    // verify!(does_not_have_tag!(&info, SecretSanitizer<SECRET_SANITIZER>));
    let encrypted = info ^ 99991;
    add_tag!(&encrypted, SecretSanitizer<SECRET_SANITIZER>);
    // verify!(has_tag!(&encrypted, SecretTaint<SECRET_TAINT>));
    verify!(has_tag!(&encrypted, SecretSanitizer<SECRET_SANITIZER>));
}
