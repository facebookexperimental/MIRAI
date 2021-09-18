// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test for basic tracking of tags

#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

use mirai_annotations::*;

struct SecretTaintKind<const MASK: TagPropagationSet> {}

const SECRET_TAINT: TagPropagationSet = tag_propagation_set!(TagPropagation::BitOr);

type SecretTaint = SecretTaintKind<SECRET_TAINT>;

struct SecretSanitizerKind<const MASK: TagPropagationSet> {}

const SECRET_SANITIZER: TagPropagationSet = tag_propagation_set!(TagPropagation::BitXor);

type SecretSanitizer = SecretSanitizerKind<SECRET_SANITIZER>;

pub fn test(secret: i32) {
    precondition!(does_not_have_tag!(&secret, SecretTaint));
    precondition!(does_not_have_tag!(&secret, SecretSanitizer));

    add_tag!(&secret, SecretTaint);
    verify!(has_tag!(&secret, SecretTaint));
    verify!(does_not_have_tag!(&secret, SecretSanitizer));

    let info = secret | 1;
    verify!(has_tag!(&info, SecretTaint));
    verify!(does_not_have_tag!(&info, SecretSanitizer));

    let encrypted = info ^ 99991;
    add_tag!(&encrypted, SecretSanitizer);
    verify!(does_not_have_tag!(&encrypted, SecretTaint));
    verify!(has_tag!(&encrypted, SecretSanitizer));

    let temp = encrypted ^ 10003;
    verify!(does_not_have_tag!(&temp, SecretTaint));
    verify!(has_tag!(&temp, SecretSanitizer));

    let polluted = temp | secret;
    verify!(has_tag!(&polluted, SecretTaint));
    verify!(does_not_have_tag!(&polluted, SecretSanitizer));
}

pub fn main() {}
