// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test to see that functions accessed via fields and indirections are passed in during analysis

use mirai_annotations::*;

pub struct ContainsFunc {
    pub func: fn() -> i32,
}

fn t1a(cf: &ContainsFunc) -> i32 {
    (cf.func)()
}

pub fn t1() {
    let cf = ContainsFunc { func: || 1 };
    let r = t1a(&cf);
    verify!(r == 1);
}

pub struct SmugglesFunc<'a> {
    pub smuggle: &'a ContainsFunc,
}

fn t2a(sf: &SmugglesFunc) -> i32 {
    (sf.smuggle.func)()
}

pub fn t2() {
    let cf = ContainsFunc { func: || 1 };
    let sf = SmugglesFunc { smuggle: &cf };
    let r = t2a(&sf);
    verify!(r == 1);
}

pub struct ContainsFuncRef<'a> {
    pub func_ref: &'a dyn Fn() -> i32,
}

pub struct SmugglesFuncRef<'a> {
    pub smuggle: &'a ContainsFuncRef<'a>,
}

fn t3a(sf: &SmugglesFuncRef) -> i32 {
    (sf.smuggle.func_ref)()
}

pub fn t3() {
    let f = || 1;
    let cf = ContainsFuncRef { func_ref: &|| f() };
    let sf = SmugglesFuncRef { smuggle: &cf };
    let r = t3a(&sf);
    verify!(r == 1);
}

pub fn main() {}
