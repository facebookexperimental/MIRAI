// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use abstract_value::{AbstractValue, Path};
use rpds::{HashTrieMap, List};
use rustc::session::config::{self, ErrorOutputType, Input};
use rustc::session::Session;
use rustc_codegen_utils::codegen_backend::CodegenBackend;
use rustc_driver::{driver, Compilation, CompilerCalls, RustcDefaultCalls};
use rustc_metadata::cstore::CStore;
use std::path::PathBuf;
use summaries;
use syntax::{ast, errors};
use visitors;
use visitors::MirVisitor;

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
        match input {
            Input::File(path_buf) => info!("Processing input file: {}", path_buf.display()),
            Input::Str { input, .. } => info!("Processing input string: {}", input),
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
        controller.after_analysis.callback = Box::new(move |state| after_analysis(state));
        // Note: the callback is only invoked if the compiler discovers no errors beforehand.
        controller
    }
}

/// Called after the compiler has completed all analysis passes and before it lowers MIR to LLVM IR.
/// At this point the compiler is ready to tell us all it knows and we can proceed to do abstract
/// interpretation of all of the functions that will end up in the compiler output.
fn after_analysis(state: &mut driver::CompileState) {
    let tcx = state.tcx.unwrap();
    let crate_name: &str = state.crate_name.unwrap();
    let summary_store_path: String = String::from(".summary_store.rocksdb");
    let mut persistent_summary_cache =
        summaries::PersistentSummaryCache::new(&tcx, crate_name, summary_store_path);
    for def_id in tcx.body_owners() {
        let name = summaries::summary_key_str(&tcx, crate_name, def_id);
        info!("analyzing({:?})", name);
        // By this time all analyses have been carried out, so it should be safe to borrow this now.
        let mir = tcx.optimized_mir(def_id);
        let mut environment: HashTrieMap<Path, AbstractValue> = HashTrieMap::new();
        let mut inferred_preconditions: List<AbstractValue> = List::new();
        let mut path_conditions: List<AbstractValue> = List::new();
        let mut preconditions: List<AbstractValue> = List::new();
        let mut post_conditions: List<AbstractValue> = List::new();
        let mut unwind_condition: Option<AbstractValue> = None;
        {
            let mir_visitor = visitors::MirTestVisitor {
                tcx,
                def_id,
                mir,
                environment: &mut environment,
                inferred_preconditions: &mut inferred_preconditions,
                path_conditions: &mut path_conditions,
                preconditions: &mut preconditions,
                post_conditions: &mut post_conditions,
                unwind_condition: &mut unwind_condition,
                summary_cache: &mut persistent_summary_cache,
            };
            mir_visitor.visit_body();
        }
        let summary = summaries::summarize(
            environment,
            inferred_preconditions,
            path_conditions,
            preconditions,
            post_conditions,
            unwind_condition,
        );
        persistent_summary_cache.set_summary_for(def_id, summary);
    }
    info!("done with analysis");
}
