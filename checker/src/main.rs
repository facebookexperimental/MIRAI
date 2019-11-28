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
extern crate rustc;
extern crate rustc_driver;
extern crate rustc_interface;

use log::info;
use mirai::callbacks;
use mirai::options::Options;
use mirai::utils;
use rustc::session::config::ErrorOutputType;
use rustc::session::early_error;
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

    // Get MIRAI options from environment variable. For now, we do not pass them
    // on the command line because `RUSTC_WRAPPER=mirai cargo build` does not accept any
    // options and arguments which it does not known about (even though we could remove them in
    // this code here and not pass on to rustc). Once we have cargo integration
    // of MIRAI we may want to change this.
    let mut options = Options::default();
    let rustc_args = if env::var("MIRAI_FLAGS").is_ok() {
        options.parse_from_str(&env::var("MIRAI_FLAGS").ok().unwrap())
    } else {
        vec![]
    };
    info!("Options: {:?}", options);

    rustc_driver::install_ice_hook();
    let result = rustc_driver::catch_fatal_errors(|| {
        // Get command line arguments from environment and massage them a bit.
        let mut command_line_arguments = env::args_os()
            .enumerate()
            .map(|(i, arg)| {
                arg.into_string().unwrap_or_else(|arg| {
                    early_error(
                        ErrorOutputType::default(),
                        &format!("Argument {} is not valid Unicode: {:?}", i, arg),
                    )
                })
            })
            .collect::<Vec<_>>();

        // Setting RUSTC_WRAPPER causes Cargo to pass 'rustc' as the first argument.
        // We're invoking the compiler programmatically, so we remove it if present.
        if command_line_arguments.len() > 1
            && Path::new(&command_line_arguments[1]).file_stem() == Some("rustc".as_ref())
        {
            command_line_arguments.remove(1);
        }

        let sysroot: String = "--sysroot".into();
        if !command_line_arguments
            .iter()
            .any(|arg| arg.starts_with(&sysroot))
        {
            // Tell compiler where to find the std library and so on.
            // The compiler relies on the standard rustc driver to tell it, so we have to do likewise.
            command_line_arguments.push(sysroot);
            command_line_arguments.push(utils::find_sysroot());
        }

        let always_encode_mir: String = "always-encode-mir".into();
        if !command_line_arguments
            .iter()
            .any(|arg| arg.ends_with(&always_encode_mir))
        {
            // Tell compiler to emit MIR into crate for every function with a body.
            command_line_arguments.push("-Z".into());
            command_line_arguments.push(always_encode_mir);
        }

        // Add any arguments obtained from MIRAI_FLAGS following `--`
        command_line_arguments.extend(rustc_args);

        let mut callbacks = callbacks::MiraiCallbacks::new(options);
        rustc_driver::run_compiler(
            &command_line_arguments,
            &mut callbacks,
            None, // use default file loader
            None, // emit output to default destination
        )
    })
    .and_then(|result| result);
    let exit_code = match result {
        Ok(_) => rustc_driver::EXIT_SUCCESS,
        Err(_) => rustc_driver::EXIT_FAILURE,
    };
    std::process::exit(exit_code);
}
