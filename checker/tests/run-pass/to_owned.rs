// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test for transmutation of floating point numbers to integers

// use mirai_annotations::*;
//
// pub struct Identifier(Box<str>);
//
// // The transparent attribute is required for the test
// #[repr(transparent)]
// pub struct IdentStr(str);
//
// impl IdentStr {
//     pub fn to_owned(&self) -> Identifier {
//         Identifier(self.0.into())
//     }
// }
//
// pub fn t1() {
//     unsafe {
//         let id_str = std::mem::transmute::<&str, &IdentStr>("abc");
//         let id = id_str.to_owned();
//         assume!(id.0.len() == 3);
//     }
// }

pub fn main() {}
