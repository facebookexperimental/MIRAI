// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use rustc::session::config::{self, ErrorOutputType, Input};
use rustc::session::Session;
use rustc_codegen_utils::codegen_backend::CodegenBackend;
use rustc_driver::{driver, Compilation, CompilerCalls, RustcDefaultCalls};
use rustc_metadata::cstore::CStore;
use std::path::PathBuf;
use syntax::{ast, errors};

/// Private state used to implement the callbacks.
pub struct MiraiCallbacks {
    /// Use these to just defer to the Rust compiler's implementations.
    default_calls: RustcDefaultCalls,
}

/// Provides a default constructor
impl MiraiCallbacks {
    pub fn new() -> MiraiCallbacks {
        MiraiCallbacks {
            default_calls: RustcDefaultCalls,
        }
    }
}
impl Default for MiraiCallbacks {
    fn default() -> Self {
        Self::new()
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
        descriptions: &errors::registry::Registry,
        output: ErrorOutputType,
    ) -> Compilation {
        // todo: #3 extract options that are relevant to Mirai and store them in self
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
        matches: &::getopts::Matches,
        session: &Session,
        crate_store: &CStore,
        input: &Input,
        output_directory: &Option<PathBuf>,
        output_filename: &Option<PathBuf>,
    ) -> Compilation {
        // todo: #4 this is a place where some information about the analysis run can be logged
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
        // todo: #5 this is an opportunity to look for and load or construct the summaries for each input
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
        descriptions: &errors::registry::Registry,
    ) -> Option<(Input, Option<PathBuf>)> {
        // The default behavior will do for now.
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
        _matches: &::getopts::Matches,
    ) -> driver::CompileController<'a> {
        // For now we just do what rustc does, which is what basic() will return.
        let mut controller = driver::CompileController::basic();
        controller.after_analysis.callback = Box::new(move |state| after_analysis(state));
        controller
    }
}

fn after_analysis(state: &mut driver::CompileState) {
    state.session.abort_if_errors();

    let _type_context = state.tcx.unwrap();
}
