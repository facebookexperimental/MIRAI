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

extern crate env_logger;
extern crate mirai;
extern crate rustc_driver;
extern crate rustc_interface;

use mirai::callbacks;
use mirai::utils;
use std::env;
use std::path::Path;

fn main() {
    // Initialize loggers.
    if env::var("RUST_LOG").is_ok() {
        rustc_driver::init_rustc_env_logger();
    }
    if env::var("MIRAI_LOG").is_ok() {
        let e = env_logger::Env::new()
            .filter("MIRAI_LOG")
            .write_style("MIRAI_LOG_STYLE");
        env_logger::init_from_env(e);
    }

    // Get command line arguments from environment and massage them a bit.
    let mut command_line_arguments: Vec<_> = env::args().collect();

    // Setting RUSTC_WRAPPER causes Cargo to pass 'rustc' as the first argument.
    // We're invoking the compiler programmatically, so we remove it if present.
    if command_line_arguments.len() > 1
        && Path::new(&command_line_arguments[1]).file_stem() == Some("rustc".as_ref())
    {
        command_line_arguments.remove(1);
    }

    // Tell compiler where to find the std library and so on.
    // The compiler relies on the standard rustc driver to tell it, so we have to do likewise.
    command_line_arguments.push(String::from("--sysroot"));
    command_line_arguments.push(utils::find_sysroot());

    let result = rustc_driver::report_ices_to_stderr_if_any(move || {
        rustc_driver::run_compiler(
            &command_line_arguments,
            &mut callbacks::MiraiCallbacks::default(),
            None, // use default file loader
            None, // emit output to default destination
        )
    })
    .and_then(|result| result);
    std::process::exit(result.is_err() as i32);
}
