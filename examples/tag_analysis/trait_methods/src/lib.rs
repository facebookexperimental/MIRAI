// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree

// This is an example of adding tag-related annotations to trait methods.

#![cfg_attr(mirai, allow(incomplete_features), feature(const_generics))]

#[macro_use]
extern crate mirai_annotations;

#[cfg(mirai)]
use mirai_annotations::{TagPropagation, TagPropagationSet};

#[cfg(mirai)]
struct SecretTaintKind<const MASK: TagPropagationSet> {}

#[cfg(mirai)]
const SECRET_TAINT_MASK: TagPropagationSet = tag_propagation_set!(TagPropagation::SubComponent);

#[cfg(mirai)]
type SecretTaint = SecretTaintKind<SECRET_TAINT_MASK>;
#[cfg(not(mirai))]
type SecretTaint = ();

use contracts::*;

#[allow(clippy::inline_fn_without_body)]
#[contract_trait]
trait ProcessWithoutTaint {
    #[requires(does_not_have_tag!(self, SecretTaint))]
    fn process(&mut self, incr: i32);
}

struct Block {
    content: i32,
}

#[contract_trait]
impl ProcessWithoutTaint for Block {
    fn process(&mut self, incr: i32) {
        self.content += incr;
    }
}

pub fn main() {
    let mut block = Block { content: 99991 };
    verify!(does_not_have_tag!(&block, SecretTaint));
    block.process(12345);
    add_tag!(&block, SecretTaint);
    verify!(has_tag!(&block, SecretTaint));
    block.process(54321); //~ unsatisfied precondition
}
