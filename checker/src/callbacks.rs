// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
#![allow(clippy::borrowed_box)]

use crate::constant_domain::ConstantValueCache;
use crate::crate_visitor::CrateVisitor;
use crate::known_names::KnownNamesCache;
use crate::options::{DiagLevel, Options};
use crate::summaries::PersistentSummaryCache;

use crate::type_visitor::TypeCache;
use log::info;
use log_derive::*;
use rustc_driver::Compilation;
use rustc_interface::{interface, Queries};
use rustc_middle::ty::TyCtxt;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter, Result};
use std::path::PathBuf;
use std::rc::Rc;
use tempfile::TempDir;

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
                if Self::is_test_excluded(&self.file_name) {
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
    fn is_test_excluded(_file_name: &str) -> bool {
        false
    }

    fn is_excluded(&self, file_name: &str) -> bool {
        // Exclude crates that contain code that causes MIRAI to crash or not terminate within 2 hours
        if file_name.contains("client/assets-proof/src") // Sort mismatch at argument #2 for function (declare-fun + (Int Int) Int) supplied sort is <null>
            || file_name.contains("client/faucet/src") // non termination
            || file_name.contains("config/src") // entered unreachable code', checker/src/type_visitor.rs:783:25
            || file_name.contains("config/management/operational/src") // crash
            || file_name.contains("execution/execution-correctness/src") // unreachable: checker/src/body_visitor.rs:1213:38
            || file_name.contains("language/diem-vm/src") // Sorts Bool and Int are incompatible
            || file_name.contains("language/move-lang/src") // non termination
            || file_name.contains("language/move-model/src") // non termination
            || file_name.contains("language/move-prover/boogie-backend/src") // entered unreachable code', checker/src/type_visitor.rs:783:25
            || file_name.contains("language/move-prover/bytecode/src") // non termination
            || file_name.contains("language/move-prover/interpreter/src") // index out of bounds: the len is 0 but the index is 0
            || file_name.contains("language/tools/move-bytecode-viewer/src") // out of memory
            || file_name.contains("language/tools/move-coverage/src") // out of memory
            || file_name.contains("language/transaction-builder/generator/src") // entered unreachable code', checker/src/type_visitor.rs:783:25
            || file_name.contains("network/src") // could not fully normalize 
            || file_name.contains("network/builder/src") // could not fully normalize
            || file_name.contains("sdk/client/src") // non termination
            || file_name.contains("storage/backup/backup-cli/src") // out of memory
            || file_name.contains("storage/diemdb/src") // expect reference target to have a value
            || file_name.contains("types/src")
        //Sorts Int and <null> are incompatible
        {
            return true;
        }

        // Exclude crates that currently slow down testing too much
        if self.options.diag_level == DiagLevel::Default
            && (file_name.contains("client/swiss-knife/src")
                || file_name.contains("common/metrics/src")
                || file_name.contains("common/num-variants/src")
                || file_name.contains("common/rate-limiter/src")
                || file_name.contains("config/src")
                || file_name.contains("config/management/src")
                || file_name.contains("config/management/genesis/src")
                || file_name.contains("config/management/network-address-encryption/src")
                || file_name.contains("config/seed-peer-generator/src")
                || file_name.contains("consensus/safety-rules/src")
                || file_name.contains("consensus/src")
                || file_name.contains("crypto/crypto/src")
                || file_name.contains("crypto/crypto-derive/src")
                || file_name.contains("diem-node/src")
                || file_name.contains("json-rpc/src")
                || file_name.contains("language/bytecode-verifier/src")
                || file_name.contains("language/compiler/src")
                || file_name.contains("language/compiler/ir-to-bytecode/src")
                || file_name.contains("language/diem-framework/src")
                || file_name.contains("language/diem-framework/releases/src")
                || file_name.contains("language/diem-tools/diem-validator-interface")
                || file_name.contains("language/diem-tools/transaction-replay/src")
                || file_name.contains("language/diem-tools/writeset-transaction-generator/src")
                || file_name.contains("language/diem-vm/src")
                || file_name.contains("language/move-prover/src")
                || file_name.contains("language/move-prover/abigen/src")
                || file_name.contains("language/move-prover/boogie-backend-exp/src")
                || file_name.contains("language/move-prover/bytecode/src")
                || file_name.contains("language/move-prover/docgen/src")
                || file_name.contains("language/move-prover/interpreter/src")
                || file_name.contains("move-prover/errmapgen/src")
                || file_name.contains("language/move-prover/lab/src")
                || file_name.contains("language/move-stdlib/src")
                || file_name.contains("language/tools/move-cli/src")
                || file_name.contains("language/tools/move-unit-test/src")
                || file_name.contains("language/tools/read-write-set/src")
                || file_name.contains("language/tools/resource-viewer/src")
                || file_name.contains("language/tools/vm-genesis/src")
                || file_name.contains("mempool/src")
                || file_name.contains("network/builder/src")
                || file_name.contains("network/simple-onchain-discovery/src")
                || file_name.contains("sdk/src")
                || file_name.contains("secure/key-manager/src")
                || file_name.contains("secure/net/src")
                || file_name.contains("secure/storage/src")
                || file_name.contains("secure/storage/vault/src")
                || file_name.contains("state-sync/src")
                || file_name.contains("storage/schemadb/src")
                || file_name.contains("storage/storage-client/src")
                || file_name.contains("types/src")
                || file_name.contains("vm-validator/src"))
        {
            return true;
        }
        false
    }

    /// Analyze the crate currently being compiled, using the information given in compiler and tcx.
    #[logfn(TRACE)]
    fn analyze_with_mirai<'tcx>(&mut self, compiler: &interface::Compiler, tcx: TyCtxt<'tcx>) {
        if self.options.test_only {
            if Self::is_test_excluded(&self.file_name) {
                return;
            }
        } else if self.is_excluded(&self.file_name) {
            return;
        }

        let output_dir = String::from(self.output_directory.to_str().expect("valid string"));
        let summary_store_path = if std::env::var("MIRAI_SHARE_PERSISTENT_STORE").is_ok() {
            output_dir
        } else {
            let temp_dir = TempDir::new().expect("failed to create a temp dir");
            String::from(temp_dir.into_path().to_str().expect("valid string"))
        };
        info!(
            "storing summaries for {} at {}/.summary_store.sled",
            self.file_name, summary_store_path
        );
        let mut crate_visitor = CrateVisitor {
            buffered_diagnostics: Vec::new(),
            constant_time_tag_cache: None,
            constant_time_tag_not_found: false,
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
            type_cache: Rc::new(RefCell::new(TypeCache::new())),
        };
        crate_visitor.analyze_some_bodies();
    }
}
