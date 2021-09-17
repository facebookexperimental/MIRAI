// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test for adding tags to structs and checking tags on fields

#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

#[macro_use]
extern crate mirai_annotations;

pub mod with_propagation_to_sub_components {
    use mirai_annotations::{TagPropagation, TagPropagationSet};

    struct SecretTaintKind<const MASK: TagPropagationSet> {}

    const SECRET_TAINT: TagPropagationSet = tag_propagation_set!(TagPropagation::SubComponent);

    type SecretTaint = SecretTaintKind<SECRET_TAINT>;

    pub struct Foo {
        content: i32,
    }

    pub fn test1() {
        let foo = Foo { content: 99991 };
        add_tag!(&foo.content, SecretTaint);
        verify!(does_not_have_tag!(&foo, SecretTaint));
        verify!(has_tag!(&foo.content, SecretTaint));
    }

    pub fn test2() {
        let foo = Foo { content: 99991 };
        add_tag!(&foo, SecretTaint);
        verify!(has_tag!(&foo, SecretTaint));
        verify!(has_tag!(&foo.content, SecretTaint));
    }

    pub fn test3(cond: bool) {
        let left = Foo { content: 12345 };
        let right = Foo { content: 54321 };
        let join;
        if cond {
            join = &left;
        } else {
            join = &right;
        }
        add_tag!(&join.content, SecretTaint);
        verify!(does_not_have_tag!(&left, SecretTaint));
        verify!(does_not_have_tag!(&right, SecretTaint));
        verify!(has_tag!(&left.content, SecretTaint) || has_tag!(&right.content, SecretTaint));
    }

    pub fn test4(cond: bool) {
        let left = Foo { content: 12345 };
        let right = Foo { content: 54321 };
        let join;
        if cond {
            join = &left;
        } else {
            join = &right;
        }
        add_tag!(join, SecretTaint);
        verify!(has_tag!(&left, SecretTaint) || has_tag!(&right, SecretTaint));
        verify!(has_tag!(&left.content, SecretTaint) || has_tag!(&right.content, SecretTaint));
    }

    pub fn test5(foo: Foo, cond: bool) {
        precondition!(does_not_have_tag!(&foo, SecretTaint));
        let bar = Foo { content: 99991 };
        let join;
        if cond {
            join = &foo;
        } else {
            join = &bar;
        }
        add_tag!(&join.content, SecretTaint);
        verify!(does_not_have_tag!(&foo, SecretTaint));
        verify!(does_not_have_tag!(&bar, SecretTaint));
        verify!(has_tag!(&foo.content, SecretTaint) || has_tag!(&bar.content, SecretTaint));
    }

    pub fn test6(foo: Foo, cond: bool) {
        let bar = Foo { content: 99991 };
        let join;
        if cond {
            join = &foo;
        } else {
            join = &bar;
        }
        add_tag!(join, SecretTaint);
        verify!(has_tag!(&foo, SecretTaint) || has_tag!(&bar, SecretTaint));
        verify!(has_tag!(&foo.content, SecretTaint) || has_tag!(&bar.content, SecretTaint));
    }
}

pub mod without_propagation_to_sub_components {
    use mirai_annotations::TagPropagationSet;

    struct SecretTaintKind<const MASK: TagPropagationSet> {}

    const SECRET_TAINT: TagPropagationSet = tag_propagation_set!();

    type SecretTaint = SecretTaintKind<SECRET_TAINT>;

    pub struct Foo {
        content: i32,
    }

    pub fn test1() {
        let foo = Foo { content: 99991 };
        add_tag!(&foo.content, SecretTaint);
        verify!(does_not_have_tag!(&foo, SecretTaint));
        verify!(has_tag!(&foo.content, SecretTaint));
    }

    pub fn test2() {
        let foo = Foo { content: 99991 };
        add_tag!(&foo, SecretTaint);
        verify!(has_tag!(&foo, SecretTaint));
        verify!(does_not_have_tag!(&foo.content, SecretTaint));
    }

    pub fn test3(cond: bool) {
        let left = Foo { content: 12345 };
        let right = Foo { content: 54321 };
        let join;
        if cond {
            join = &left;
        } else {
            join = &right;
        }
        add_tag!(&join.content, SecretTaint);
        verify!(does_not_have_tag!(&left, SecretTaint));
        verify!(does_not_have_tag!(&right, SecretTaint));
        verify!(has_tag!(&left.content, SecretTaint) || has_tag!(&right.content, SecretTaint));
    }

    pub fn test4(cond: bool) {
        let left = Foo { content: 12345 };
        let right = Foo { content: 54321 };
        let join;
        if cond {
            join = &left;
        } else {
            join = &right;
        }
        add_tag!(join, SecretTaint);
        verify!(has_tag!(&left, SecretTaint) || has_tag!(&right, SecretTaint));
        verify!(does_not_have_tag!(&left.content, SecretTaint));
        verify!(does_not_have_tag!(&right.content, SecretTaint));
    }

    pub fn test5(foo: Foo, cond: bool) {
        precondition!(does_not_have_tag!(&foo, SecretTaint));
        let bar = Foo { content: 99991 };
        let join;
        if cond {
            join = &foo;
        } else {
            join = &bar;
        }
        add_tag!(&join.content, SecretTaint);
        verify!(does_not_have_tag!(&foo, SecretTaint));
        verify!(does_not_have_tag!(&bar, SecretTaint));
        verify!(has_tag!(&foo.content, SecretTaint) || has_tag!(&bar.content, SecretTaint));
    }

    pub fn test6(foo: Foo, cond: bool) {
        precondition!(does_not_have_tag!(&foo.content, SecretTaint));
        let bar = Foo { content: 99991 };
        let join;
        if cond {
            join = &foo;
        } else {
            join = &bar;
        }
        add_tag!(join, SecretTaint);
        verify!(has_tag!(&foo, SecretTaint) || has_tag!(&bar, SecretTaint));
        verify!(does_not_have_tag!(&foo.content, SecretTaint));
        verify!(does_not_have_tag!(&bar.content, SecretTaint));
    }
}

pub fn main() {}
