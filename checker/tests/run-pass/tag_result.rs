// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test for adding tags to Result structs

#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

use mirai_annotations::*;

struct SecretTaintKind<const MASK: TagPropagationSet> {}

type SecretTaint = SecretTaintKind<TAG_PROPAGATION_ALL>;

fn get_abs_vec_val() -> Result<Vec<u8>, ()> {
    result!()
}

pub fn test1() -> Result<(), ()> {
    let x: Result<Vec<u8>, ()> = get_abs_vec_val();
    add_tag!(&x, SecretTaint);
    let y = x?;
    verify!(has_tag!(&y, SecretTaint));
    Ok(())
}

pub fn test2() {
    let x: Result<i32, ()> = Ok(42);
    add_tag!(&x, SecretTaint);
    let y = x.or(Err(()));
    verify!(has_tag!(&y, SecretTaint)); // tag flows from x to y via TagPropagation::SuperComponent
    if let Ok(z) = y {
        verify!(has_tag!(&z, SecretTaint));
    }
}

pub fn main() {}
