// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//
// In an ideal world there would be a stable well documented set of crates containing a specific
// version of the Rust compiler along with its sources and debug information. We'd then just get
// those from crate.io and merely go on our way as just another Rust application. Rust compiler
// upgrades will be non events for Mirai until it is ready to jump to another release and old
// versions of Mirai will continue to work just as before.
//
// In the current world, however, we have to use the following hacky feature to get access to a
// private and not very stable set of APIs from whatever compiler is in the path when we run Mirai.
// While pretty bad, it is a lot less bad than having to write our own compiler, so here goes.
#![feature(rustc_private)]
#![feature(box_syntax)]
#![feature(const_vec_new)]
#![feature(vec_remove_item)]

extern crate rustc;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_target;
extern crate syntax;
extern crate syntax_pos;

pub mod abstract_domains;
pub mod abstract_value;
pub mod callbacks;
pub mod constant_domain;
pub mod environment;
pub mod expected_errors;
pub mod expression;
pub mod interval_domain;
pub mod k_limits;
pub mod smt_solver;
pub mod summaries;
pub mod utils;
pub mod visitors;
