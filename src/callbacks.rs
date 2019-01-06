// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
#![allow(clippy::borrowed_box)]

use constant_value::ConstantValueCache;
use rustc::session::config::{self, ErrorOutputType, Input};
use rustc::session::Session;
use rustc_codegen_utils::codegen_backend::CodegenBackend;
use rustc_driver::{driver, Compilation, CompilerCalls, RustcDefaultCalls};
use rustc_metadata::cstore::CStore;
use std::path::PathBuf;
use summaries;
use syntax::errors::{Diagnostic, DiagnosticBuilder};
use syntax::{ast, errors};
use visitors::{MirVisitor, MirVisitorCrateContext};

/// Private state used to implement the callbacks.
pub struct MiraiCallbacks {
    /// Called after static analysis is complete.
    /// Gives test harness a way to process intercepted diagnostics.
    consume_buffered_diagnostics: Box<Fn(&Vec<Diagnostic>) -> ()>,
    /// Use these to just defer to the Rust compiler's implementations.
    default_calls: RustcDefaultCalls,
    /// Called when static analysis reports a diagnostic message.
    /// By default, this just emits the message. When overridden it can
    /// intercept and buffer the diagnostics, which is used by the test harness.
    emit_diagnostic: fn(&mut DiagnosticBuilder, &mut Vec<Diagnostic>) -> (),
    /// A path to the directory where analysis output, such as the summary cache, should be stored.
    output_directory: PathBuf,
}

/// Constructors
impl MiraiCallbacks {
    pub fn new() -> MiraiCallbacks {
        MiraiCallbacks {
            consume_buffered_diagnostics: box |_bd: &Vec<Diagnostic>| {},
            default_calls: RustcDefaultCalls,
            emit_diagnostic: |db: &mut DiagnosticBuilder, _buf: &mut Vec<Diagnostic>| db.emit(),
            output_directory: PathBuf::default(),
        }
    }

    pub fn with_buffered_diagnostics(
        consume_buffered_diagnostics: Box<Fn(&Vec<Diagnostic>) -> ()>,
        emit_diagnostic: fn(&mut DiagnosticBuilder, &mut Vec<Diagnostic>) -> (),
    ) -> MiraiCallbacks {
        MiraiCallbacks {
            consume_buffered_diagnostics,
            default_calls: RustcDefaultCalls,
            emit_diagnostic,
            output_directory: PathBuf::default(),
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
        match input {
            Input::File(path_buf) => info!("Processing input file: {}", path_buf.display()),
            Input::Str { input, .. } => info!("Processing input string: {}", input),
        }
        match output_directory {
            None => self
                .output_directory
                .push(std::env::temp_dir().to_str().unwrap()),
            Some(path_buf) => self.output_directory.push(path_buf.as_path()),
        }
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

    /// Called when compilation starts and allows Mirai to supply the Rust compiler with a
    /// customized controller for the phases of the compilation. The controller provides hooks
    /// for further callbacks that can be used to obtain information from the
    /// compiler's internal state and that present an opportunity to do analysis of the MIR.
    fn build_controller(
        self: Box<Self>,
        _session: &Session,
        _matches: &::getopts::Matches,
    ) -> driver::CompileController<'a> {
        let mut controller = driver::CompileController::basic();
        controller.after_analysis.callback = Box::new(move |state| {
            after_analysis(
                state,
                &self.consume_buffered_diagnostics,
                self.emit_diagnostic,
                &mut self.output_directory.clone(),
            )
        });
        // Note: the callback is only invoked if the compiler discovers no errors beforehand.
        controller
    }
}

/// Called after the compiler has completed all analysis passes and before it lowers MIR to LLVM IR.
/// At this point the compiler is ready to tell us all it knows and we can proceed to do abstract
/// interpretation of all of the functions that will end up in the compiler output.
fn after_analysis(
    state: &mut driver::CompileState,
    consume_buffered_diagnostics: &Box<Fn(&Vec<Diagnostic>) -> ()>,
    emit_diagnostic: fn(&mut DiagnosticBuilder, &mut Vec<Diagnostic>) -> (),
    output_directory: &mut PathBuf,
) {
    let mut buffered_diagnostics: Vec<Diagnostic> = vec![];
    let session = state.session;
    let tcx = state.tcx.unwrap();
    output_directory.set_file_name(".summary_store");
    output_directory.set_extension("rocksdb");
    let summary_store_path = String::from(output_directory.to_str().unwrap());
    info!("storing summaries at {}", summary_store_path);
    let mut persistent_summary_cache =
        summaries::PersistentSummaryCache::new(&tcx, summary_store_path);
    let mut constant_value_cache = ConstantValueCache::default();
    for def_id in tcx.body_owners() {
        {
            let name = persistent_summary_cache.get_summary_key_for(def_id);
            info!("analyzing({:?})", name);
        }
        // By this time all analyses have been carried out, so it should be safe to borrow this now.
        let mir = tcx.optimized_mir(def_id);
        let mut mir_visitor = MirVisitor::new(MirVisitorCrateContext {
            buffered_diagnostics: &mut buffered_diagnostics,
            emit_diagnostic,
            session,
            tcx,
            def_id,
            mir,
            summary_cache: &mut persistent_summary_cache,
            constant_value_cache: &mut constant_value_cache,
        });
        mir_visitor.visit_body();
    }
    consume_buffered_diagnostics(&buffered_diagnostics);
    info!("done with analysis");
}
