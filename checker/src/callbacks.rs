// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
#![allow(clippy::borrowed_box)]

use crate::constant_domain::ConstantValueCache;
use crate::crate_visitor::CrateVisitor;
use crate::known_names::KnownNamesCache;
use crate::options::Options;
use crate::summaries::PersistentSummaryCache;

use log::info;
use log_derive::*;
use rustc_driver::Compilation;
use rustc_interface::{interface, Queries};
use rustc_middle::ty::TyCtxt;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter, Result};
use std::path::PathBuf;
use tempdir::TempDir;

/// Private state used to implement the callbacks.
pub struct MiraiCallbacks {
    /// Options provided to the analysis.
    options: Options,
    /// The relative path of the file being compiled.
    file_name: String,
    /// A path to the directory where analysis output, such as the summary cache, should be stored.
    output_directory: PathBuf,
    /// True if this run is done via cargo test
    test_run: bool,
}

/// Constructors
impl MiraiCallbacks {
    pub fn new(options: Options) -> MiraiCallbacks {
        MiraiCallbacks {
            options,
            file_name: String::new(),
            output_directory: PathBuf::default(),
            test_run: false,
        }
    }

    pub fn test_runner(options: Options) -> MiraiCallbacks {
        MiraiCallbacks {
            options,
            file_name: String::new(),
            output_directory: PathBuf::default(),
            test_run: true,
        }
    }
}

impl Debug for MiraiCallbacks {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "MiraiCallbacks".fmt(f)
    }
}

impl Default for MiraiCallbacks {
    fn default() -> Self {
        Self::new(Options::default())
    }
}

impl rustc_driver::Callbacks for MiraiCallbacks {
    /// Called before creating the compiler instance
    #[logfn(TRACE)]
    fn config(&mut self, config: &mut interface::Config) {
        self.file_name = config.input.source_name().to_string();
        info!("Processing input file: {}", self.file_name);
        if self.options.test_only {
            if config.opts.test {
                if Self::is_test_black_listed(&self.file_name) {
                    // This file is known not to compile with the test flag.
                    // This happens in Libra code.
                    std::process::exit(0);
                }
            } else {
                // In test only mode we only run MIRAI when the --tests flag has been set.
                return;
            }
        }

        config.crate_cfg.insert(("mirai".to_string(), None));
        match &config.output_dir {
            None => {
                self.output_directory = std::env::temp_dir();
                self.output_directory.pop();
            }
            Some(path_buf) => self.output_directory.push(path_buf.as_path()),
        };
    }

    /// Called after the compiler has completed all analysis passes and before it lowers MIR to LLVM IR.
    /// At this point the compiler is ready to tell us all it knows and we can proceed to do abstract
    /// interpretation of all of the functions that will end up in the compiler output.
    /// If this method returns false, the compilation will stop.
    #[logfn(TRACE)]
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();
        if self.options.test_only && !compiler.session().opts.test {
            // In test only mode we only run MIRAI when the --tests flag has been set.
            return Compilation::Continue;
        }
        if self
            .output_directory
            .to_str()
            .expect("valid string")
            .contains("/build/")
        {
            // No need to analyze a build script, but do generate code.
            return Compilation::Continue;
        }
        queries
            .global_ctxt()
            .unwrap()
            .peek_mut()
            .enter(|tcx| self.analyze_with_mirai(compiler, tcx));
        if self.test_run {
            // We avoid code gen for test cases because LLVM is not used in a thread safe manner.
            Compilation::Stop
        } else {
            // Although MIRAI is only a checker, cargo still needs code generation to work.
            Compilation::Continue
        }
    }
}

impl MiraiCallbacks {
    fn is_test_black_listed(file_name: &str) -> bool {
        file_name.contains("storage/storage-service/src") || file_name.contains("client/cli/src")
    }

    fn is_black_listed(file_name: &str) -> bool {
        file_name.contains("admission-control/admission-control-proto/src") // resolve error
            || file_name.contains("consensus/src") // resolve error
            || file_name.contains("crypto/crypto/src") // false positives
            || file_name.contains("crypto/crypto-derive/src") // false positives
            || file_name.contains("common/bitvec/src") // false positives
            || file_name.contains("common/bounded-executor/src") // false positive: possible assertion failed: ptr.as_ptr() as usize & NUM_FLAG == 0
            || file_name.contains("common/debug-interface/src") // false positives
            || file_name.contains("common/futures-semaphore/src") // false positive: possible assertion failed: ptr.as_ptr() as usize & NUM_FLAG == 0
            || file_name.contains("common/logger/src") // z3 encoding
            || file_name.contains("common/metrics/src") // false positives
            || file_name.contains("language/bytecode-verifier/src") // false positives
            || file_name.contains("language/compiler/bytecode-source-map/src") // false positives
            || file_name.contains("language/compiler/ir-to-bytecode/syntax/src") // false positives
            || file_name.contains("language/resource-viewer/src") // z3 encoding
            || file_name.contains("language/stdlib/src") // false positives
            || file_name.contains("language/move-lang/src") // resolve error
            || file_name.contains("language/move-vm/state/src") // false positives
            || file_name.contains("language/vm/src") // takes too long
            || file_name.contains("network/src") // false positives
            || file_name.contains("network/onchain-discovery/src") // false positives
            || file_name.contains("client/cli/src") // false positives   
            || file_name.contains("client/libra_wallet/src") // false positive: self.execute(offset, len, |buffer| dst[..len].copy_from_slice(buffer));
            || file_name.contains("secure/net/src") // false positives
            || file_name.contains("secure/storage/vault/src") // z3 encoding
            || file_name.contains("state-synchronizer/src") // false positives
            || file_name.contains("storage/jellyfish-merkle/src") // false positives due to complex loops beyond what we can handle right now
            || file_name.contains("storage/libradb/src") // 'already borrowed: BorrowMutError'
            || file_name.contains("storage/scratchpad/src") // false positives
            || file_name.contains("testsuite/cli/src") // false positives
            || file_name.contains("types/src") // resolve error
    }

    /// Analyze the crate currently being compiled, using the information given in compiler and tcx.
    #[logfn(TRACE)]
    fn analyze_with_mirai<'tcx>(&mut self, compiler: &interface::Compiler, tcx: TyCtxt<'tcx>) {
        if self.options.test_only {
            if Self::is_test_black_listed(&self.file_name) {
                return;
            }
        } else if Self::is_black_listed(&self.file_name) {
            return;
        }

        let output_dir = String::from(self.output_directory.to_str().expect("valid string"));
        let summary_store_path = if std::env::var("MIRAI_SHARE_PERSISTENT_STORE").is_ok() {
            output_dir
        } else {
            let temp_dir = TempDir::new("mirai_temp_dir").expect("failed to create a temp dir");
            String::from(temp_dir.into_path().to_str().expect("valid string"))
        };
        info!(
            "storing summaries for {} at {}/.summary_store.sled",
            self.file_name, summary_store_path
        );
        let mut crate_visitor = CrateVisitor {
            buffered_diagnostics: Vec::new(),
            constant_value_cache: ConstantValueCache::default(),
            diagnostics_for: HashMap::new(),
            file_name: self.file_name.as_str(),
            known_names_cache: KnownNamesCache::create_cache_from_language_items(),
            options: &std::mem::take(&mut self.options),
            session: compiler.session(),
            substs_cache: HashMap::new(),
            summary_cache: PersistentSummaryCache::new(tcx, summary_store_path),
            tcx,
            test_run: self.test_run,
        };
        crate_visitor.analyze_some_bodies();
    }
}
