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
extern crate rustc_session;

use itertools::Itertools;
use log::*;
use mirai::callbacks;
use mirai::options::Options;
use mirai::utils;
use mirai_annotations::*;
use rustc_session::config::ErrorOutputType;
use rustc_session::early_error;
use std::env;
use std::path::Path;

fn main() {
    // Initialize loggers.
    if env::var("RUSTC_LOG").is_ok() {
        rustc_driver::init_rustc_env_logger();
    }
    if env::var("MIRAI_LOG").is_ok() {
        let e = env_logger::Env::new()
            .filter("MIRAI_LOG")
            .write_style("MIRAI_LOG_STYLE");
        env_logger::init_from_env(e);
    }

    // Get any options specified via the MIRAI_FLAGS environment variable
    let mut options = Options::default();
    let rustc_args = options.parse_from_str(&env::var("MIRAI_FLAGS").unwrap_or_default(), false);
    info!("MIRAI options from environment: {:?}", options);

    // Let arguments supplied on the command line override the environment variable.
    let mut args = env::args_os()
        .enumerate()
        .map(|(i, arg)| {
            arg.into_string().unwrap_or_else(|arg| {
                early_error(
                    ErrorOutputType::default(),
                    &format!("Argument {i} is not valid Unicode: {arg:?}"),
                )
            })
        })
        .collect::<Vec<_>>();
    assume!(!args.is_empty());

    // Setting RUSTC_WRAPPER causes Cargo to pass 'rustc' as the first argument.
    // We're invoking the compiler programmatically, so we remove it if present.
    if args.len() > 1 && Path::new(&args[1]).file_stem() == Some("rustc".as_ref()) {
        args.remove(1);
    }

    let mut rustc_command_line_arguments = options.parse(&args[1..], false);
    info!("MIRAI options modified by command line: {:?}", options);

    rustc_driver::install_ice_hook();
    let result = rustc_driver::catch_fatal_errors(|| {
        // Add back the binary name
        rustc_command_line_arguments.insert(0, args[0].clone());

        let print: String = "--print=".into();
        if rustc_command_line_arguments
            .iter()
            .any(|arg| arg.starts_with(&print))
        {
            // If a --print option is given on the command line we wont get called to analyze
            // anything. We also don't want to the caller to know that MIRAI adds configuration
            // parameters to the command line, lest the caller be cargo and it panics because
            // the output from --print=cfg is not what it expects.
        } else {
            // Add rustc arguments supplied via the MIRAI_FLAGS environment variable
            rustc_command_line_arguments.extend(rustc_args);

            let sysroot: String = "--sysroot".into();
            if !rustc_command_line_arguments
                .iter()
                .any(|arg| arg.starts_with(&sysroot))
            {
                // Tell compiler where to find the std library and so on.
                // The compiler relies on the standard rustc driver to tell it, so we have to do likewise.
                rustc_command_line_arguments.push(sysroot);
                rustc_command_line_arguments.push(utils::find_sysroot());
            }

            let always_encode_mir: String = "always-encode-mir".into();
            if !rustc_command_line_arguments
                .iter()
                .any(|arg| arg.ends_with(&always_encode_mir))
            {
                // Tell compiler to emit MIR into crate for every function with a body.
                rustc_command_line_arguments.push("-Z".into());
                rustc_command_line_arguments.push(always_encode_mir);
            }

            if options.test_only {
                let prefix: String = "mirai_annotations=".into();
                let postfix: String = ".rmeta".into();

                if let Some((_, s)) = rustc_command_line_arguments
                    .iter_mut()
                    .find_position(|arg| arg.starts_with(&prefix))
                {
                    if s.ends_with(&postfix) {
                        *s = s.replace(&postfix, ".rlib");
                    }
                }
            }
        }

        let mut callbacks = callbacks::MiraiCallbacks::new(options);
        debug!(
            "rustc_command_line_arguments {:?}",
            rustc_command_line_arguments
        );
        let compiler =
            rustc_driver::RunCompiler::new(&rustc_command_line_arguments, &mut callbacks);
        compiler.run()
    })
    .and_then(|result| result);
    let exit_code = match result {
        Ok(_) => rustc_driver::EXIT_SUCCESS,
        Err(_) => rustc_driver::EXIT_FAILURE,
    };
    std::process::exit(exit_code);
}
