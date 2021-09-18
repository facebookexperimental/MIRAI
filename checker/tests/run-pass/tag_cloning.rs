// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test for cloning of tags

#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

use mirai_annotations::*;

#[derive(Clone)]
pub struct Block {
    pub content: i32,
}

struct TaintTagKind<const MASK: TagPropagationSet> {}

const TAINT_TAG_MASK: TagPropagationSet = tag_propagation_set!();

type TaintTag = TaintTagKind<TAINT_TAG_MASK>;

pub fn main() {
    let a = Block { content: 0 };
    add_tag!(&a, TaintTag);
    let b = a.clone();
    verify!(has_tag!(&b, TaintTag));
}
