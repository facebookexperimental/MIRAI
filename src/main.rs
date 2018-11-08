// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

#![feature(box_syntax)]
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
extern crate getopts;
extern crate rustc;
extern crate rustc_codegen_utils;
extern crate rustc_driver;
extern crate rustc_metadata;
extern crate syntax;

use rustc::session::config::{self, ErrorOutputType, Input};
use rustc::session::Session;
use rustc_codegen_utils::codegen_backend::CodegenBackend;
use rustc_driver::{driver, Compilation, CompilerCalls, RustcDefaultCalls};
use rustc_metadata::cstore::CStore;
use std::path::{Path, PathBuf};
use syntax::{ast, errors};

/// Private state used to implement the callbacks.
struct MiraiCallbacks {
    /// Use these to just defer to the Rust compiler's implementations.
    default_calls: RustcDefaultCalls,
}

/// Provides a default constructor
impl MiraiCallbacks {
    fn new() -> MiraiCallbacks {
        MiraiCallbacks {
            default_calls: RustcDefaultCalls,
        }
    }
}

/// Implements a trait for customizing the compilation process. Implements a number of call backs
/// for executing custom code or customizing input.
impl<'a> CompilerCalls<'a> for MiraiCallbacks {
    /// Called early in the process of handling arguments. This will
    /// be called straight after options have been parsed but before anything
    /// else (e.g., selecting input and output).
    fn early_callback(
        &mut self,
        matches: &::getopts::Matches,
        options: &config::Options,
        config: &ast::CrateConfig,
        descriptions: &::errors::registry::Registry,
        output: ::ErrorOutputType,
    ) -> Compilation {
        // todo: #1 extract options that are relevant to Mirai and store them in self
        // also remove these arguments so that Rustc does not try to process them
        // and possibly also add arguments here to make the compilation process more
        // friendly to static analysis.
        self.default_calls
            .early_callback(matches, options, config, descriptions, output)
    }

    /// Called late in the process of handling arguments. This will
    /// be called just before actual compilation starts (and before build_controller
    /// is called), after all arguments etc. have been completely handled.
    fn late_callback(
        &mut self,
        codegen_backend: &CodegenBackend,
        matches: &getopts::Matches,
        session: &Session,
        crate_store: &CStore,
        input: &Input,
        output_directory: &Option<PathBuf>,
        output_filename: &Option<PathBuf>,
    ) -> Compilation {
        // todo: this is a place where some information about the analysis run can be logged
        // for debugging purposes
        self.default_calls.late_callback(
            codegen_backend,
            matches,
            session,
            crate_store,
            input,
            output_directory,
            output_filename,
        )
    }

    /// Called after the compiler has extracted the input from the arguments.
    /// Gives Mirai an opportunity to change the inputs or to add some custom input handling.
    fn some_input(
        &mut self,
        input: Input,
        input_path: Option<PathBuf>,
    ) -> (Input, Option<PathBuf>) {
        // todo: this is an opportunity to look for and load or construct the summaries for each input
        self.default_calls.some_input(input, input_path)
    }

    /// Called after the compiler extracted the input from the arguments, if there were no valid
    /// input. Gives Mirai an opportunity to supply alternate input (by
    /// returning a Some value) or to add custom behaviour for this error such as
    /// emitting error messages. Returning None will cause compilation to stop
    /// at this point.
    fn no_input(
        &mut self,
        matches: &::getopts::Matches,
        options: &config::Options,
        config: &ast::CrateConfig,
        output_directory: &Option<PathBuf>,
        output_filename: &Option<PathBuf>,
        descriptions: &::errors::registry::Registry,
    ) -> Option<(Input, Option<PathBuf>)> {
        // The default behavior will do for now.
        // todo: Does the default behavior actually result in a decent error message?
        self.default_calls.no_input(
            matches,
            options,
            config,
            output_directory,
            output_filename,
            descriptions,
        )
    }

    /// Called when compilation starts and allows Mirai to supply the Rust compiler with a
    /// customized controller for the phases of the compilation. The controller provides hooks
    /// for further callbacks that can be used to obtain information from the
    /// compiler's internal state and that present an opportunity to do analysis of the MIR.
    fn build_controller(
        self: Box<Self>,
        _session: &Session,
        _matches: &getopts::Matches,
    ) -> driver::CompileController<'a> {
        // For now we just do what rustc does, which is what basic() will return.
        driver::CompileController::basic()
    }
}

fn find_sysroot() -> String {
    let home = option_env!("RUSTUP_HOME");
    let toolchain = option_env!("RUSTUP_TOOLCHAIN");
    match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .expect(
                "Could not find sysroot. Specify the RUST_SYSROOT environment variable, \
                 or use rustup to set the compiler to use for Mirai",
            )
            .to_owned(),
    }
}

fn main() {
    rustc_driver::run(|| {
        rustc_driver::init_rustc_env_logger();
        let mut command_line_arguments: Vec<_> = std::env::args().collect();

        // Setting RUSTC_WRAPPER causes Cargo to pass 'rustc' as the first argument.
        // We're invoking the compiler programmatically, so we ignore this.
        if command_line_arguments.len() <= 1 {
            std::process::exit(1);
        }
        if Path::new(&command_line_arguments[1]).file_stem() == Some("rustc".as_ref()) {
            // we still want to be able to invoke it normally though
            command_line_arguments.remove(1);
        }

        // Tell compiler where to find the std library and so on.
        // Have to do this here because the standard rustc driver does it and we are replacing it.
        command_line_arguments.push(String::from("--sysroot"));
        command_line_arguments.push(find_sysroot());
        // todo figure out how and where summaries will be written to
        rustc_driver::run_compiler(
            &command_line_arguments,
            box MiraiCallbacks::new(),
            None, // use default file loader
            None, // emit output to default destination
        )
    });
}
