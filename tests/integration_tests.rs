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

extern crate mirai;
extern crate rustc_driver;

use mirai::callbacks;
use mirai::utils;

#[test]
fn invoke_driver() {
    rustc_driver::run(|| {
        let command_line_arguments: Vec<String> = vec![
            String::from("--crate-name mirai"),
            String::from("tests/run-pass/crate_traversal.rs"),
            String::from("--crate-type"),
            String::from("lib"),
            String::from("-C"),
            String::from("debuginfo=2"),
            String::from("--out-dir"),
            String::from(std::env::temp_dir().to_str().unwrap()),
            String::from("--sysroot"),
            utils::find_sysroot(),
        ];

        rustc_driver::run_compiler(
            &command_line_arguments,
            box callbacks::MiraiCallbacks::default(),
            None, // use default file loader
            None, // emit output to default destination
        )
    });
}

#[test]
fn invoke_driver_with_no_input() {
    rustc_driver::run(|| {
        let command_line_arguments: Vec<String> = vec![
            String::from("--crate-name mirai"),
            String::from("--crate-type"),
            String::from("lib"),
            String::from("-C"),
            String::from("debuginfo=2"),
            String::from("--out-dir"),
            String::from(std::env::temp_dir().to_str().unwrap()),
            String::from("--sysroot"),
            utils::find_sysroot(),
        ];

        rustc_driver::run_compiler(
            &command_line_arguments,
            box callbacks::MiraiCallbacks::default(),
            None, // use default file loader
            None, // emit output to default destination
        )
    });
}

#[test]
fn invoke_driver_with_string_input() {
    rustc_driver::run(|| {
        let command_line_arguments: Vec<String> = vec![
            String::from("--crate-name mirai"),
            String::from("-"),
            String::from("--crate-type"),
            String::from("lib"),
            String::from("-C"),
            String::from("debuginfo=2"),
            String::from("--out-dir"),
            String::from(std::env::temp_dir().to_str().unwrap()),
            String::from("--sysroot"),
            utils::find_sysroot(),
        ];

        rustc_driver::run_compiler(
            &command_line_arguments,
            box callbacks::MiraiCallbacks::default(),
            None, // use default file loader
            None, // emit output to default destination
        )
    });
}
