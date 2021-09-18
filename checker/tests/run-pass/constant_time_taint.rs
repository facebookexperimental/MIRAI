// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test for verifying constant-time security via taint analysis

// MIRAI_FLAGS --constant_time ConstantTimeTaintKind

#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

use mirai_annotations::*;

use mirai_annotations::{TagPropagationSet, TAG_PROPAGATION_ALL};

struct ConstantTimeTaintKind<const MASK: TagPropagationSet> {}

type ConstantTimeTaint = ConstantTimeTaintKind<TAG_PROPAGATION_ALL>;

pub fn test1(secret: i32) -> i32 {
    precondition!(has_tag!(&secret, ConstantTimeTaint));
    if secret ^ 99991 > 5 {
        0
    } else {
        1
    }
    //~ the branch condition has a ConstantTimeTaintKind tag
}

pub fn test2(secret: i32) {
    precondition!(has_tag!(&secret, ConstantTimeTaint));
    let mut info = 0;
    while info != secret {
        info = info.saturating_add(1);
    }
    //~ the branch condition has a ConstantTimeTaintKind tag
}

pub fn test3(secret: i32) {
    precondition!(has_tag!(&secret, ConstantTimeTaint));
    let _ = if secret | 99991 < 5 { 32767 } else { 10003 };
    //~ the branch condition has a ConstantTimeTaintKind tag
}

pub fn test4(secret: i32, public: i32) -> i32 {
    precondition!(has_tag!(&secret, ConstantTimeTaint));
    precondition!(does_not_have_tag!(&public, ConstantTimeTaint));
    let mut result = secret;
    let mut i = public;
    while i < 99991 {
        if i < 10007 {
            result = result ^ i;
        } else {
            result = result.saturating_add(23333);
        }
        i = i + 1;
    }
    result
}

pub fn test5(v: &[i32; 4]) {
    precondition!(
        has_tag!(&v[0], ConstantTimeTaint)
            && does_not_have_tag!(&v[1], ConstantTimeTaint)
            && has_tag!(&v[2], ConstantTimeTaint)
            && does_not_have_tag!(&v[3], ConstantTimeTaint)
    );
    let mut i = 0;
    while i < 4 {
        if i % 2 != 0 {
            if v[i] > 0 {
            } else {
            }
        }
        i = i + 1;
    }
}

fn work_on_non_secret(non_secret: i32) {
    if non_secret > 5 {
    } else {
    }
}

pub fn test6() {
    let non_secret = 99991;
    verify!(does_not_have_tag!(&non_secret, ConstantTimeTaint));
    work_on_non_secret(non_secret);
}

pub fn test7(mut message: Vec<u8>) {
    precondition!(does_not_have_tag!(&message, ConstantTimeTaint));
    for m in 0..message.len() - 1 {
        message[m] = message[m] + 1;
    }
}

pub fn main() {}
