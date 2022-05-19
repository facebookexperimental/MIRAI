// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test for adding tags to vectors and vector elements

#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

//todo: fix timeout
// #[macro_use]
// extern crate mirai_annotations;
//
// pub mod propagation_for_vectors {
//     use mirai_annotations::{TagPropagation, TagPropagationSet};
//
//     struct SecretTaintKind<const MASK: TagPropagationSet> {}
//
//     const SECRET_TAINT: TagPropagationSet =
//         tag_propagation_set!(TagPropagation::SubComponent, TagPropagation::SuperComponent);
//
//     type SecretTaint = SecretTaintKind<SECRET_TAINT>;
//
//     pub struct Foo {
//         pub content: i32,
//     }
//
//     pub fn test1() {
//         let mut bar: Vec<Foo> = vec![];
//         bar.push(Foo { content: 0 });
//         add_tag!(&bar, SecretTaint);
//         verify!(has_tag!(&bar, SecretTaint));
//     }
//
//     pub fn test2() {
//         let mut bar: Vec<Foo> = vec![];
//         bar.push(Foo { content: 0 });
//         add_tag!(&bar[0], SecretTaint);
//         verify!(has_tag!(&bar[0], SecretTaint));
//     }
//
//     pub fn test3() {
//         let mut bar: Vec<Foo> = vec![];
//         bar.push(Foo { content: 0 });
//         add_tag!(&bar[0].content, SecretTaint);
//         verify!(has_tag!(&bar[0].content, SecretTaint));
//     }
//
//     pub fn test4() {
//         let mut bar: Vec<Foo> = vec![];
//         bar.push(Foo { content: 0 });
//         add_tag!(&bar, SecretTaint);
//         verify!(has_tag!(&bar[0], SecretTaint));
//     }
//
//     pub fn test5() {
//         // Iteration should not affect tag propagation on vectors
//         let mut bar: Vec<Foo> = vec![];
//         bar.push(Foo { content: 0 });
//         add_tag!(&bar, SecretTaint);
//         for foo in bar.iter() {
//             println!("{}", foo.content);
//         }
//         verify!(has_tag!(&bar, SecretTaint));
//     }
//
//     pub fn test6() {
//         let mut bar: Vec<Foo> = vec![];
//         bar.push(Foo { content: 0 });
//         add_tag!(&bar[0], SecretTaint);
//         for foo in bar.iter() {
//             println!("{}", foo.content);
//         }
//         verify!(has_tag!(&bar[0], SecretTaint));
//     }
//
//     pub fn test7() {
//         let mut bar: Vec<Foo> = vec![];
//         bar.push(Foo { content: 0 });
//         for foo in bar.iter() {
//             add_tag!(foo, SecretTaint);
//         }
//         verify!(has_tag!(&bar, SecretTaint));
//         verify!(has_tag!(&bar[0], SecretTaint));
//     }
//
//     pub fn test8() {
//         let mut bar: Vec<Foo> = vec![];
//         bar.push(Foo { content: 0 });
//         for foo in bar.iter() {
//             add_tag!(foo, SecretTaint);
//         }
//         for foo in bar.iter() {
//             verify!(has_tag!(foo, SecretTaint)); // ~ possible false verification condition
//         }
//     }
//
//     pub fn test9() {
//         let mut bar: Vec<Foo> = vec![];
//         bar.push(Foo { content: 0 });
//         for i in 0..bar.len() {
//             add_tag!(&bar[i], SecretTaint);
//         }
//         for i in 0..bar.len() {
//             verify!(has_tag!(&bar[i], SecretTaint));
//         }
//     }
// }

pub fn main() {}
