// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
#![allow(clippy::borrowed_box)]

use crate::call_graph::CallGraph;
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
        self.file_name = config.input.source_name().prefer_remapped().to_string();
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
        // Exclude crates that contain code that causes MIRAI to crash
        if file_name.starts_with("consensus/consensus-types/src") // (ite (= 1 0) 1 (ite a!1 1 0))) at position 1 does not match declaration
            || file_name.starts_with("language/diem-framework/src") // expect reference target to have a value
            || file_name.starts_with("language/diem-tools/transaction-replay/src") // 'Not a type: DefIndex(3082)'
            || file_name.starts_with("language/move-prover/boogie-backend/src") // entered unreachable code', checker/src/type_visitor.rs:783:25
            || file_name.starts_with("language/move-prover/docgen/src") //  Unexpected representation of upvar types tuple Param(<upvars>/
            || file_name.starts_with("language/tools/move-coverage/src") // out of memory
            || file_name.starts_with("language/transaction-builder/generator/src") // entered unreachable code', checker/src/type_visitor.rs:783:25
            || file_name.starts_with("network/netcore/src")
        // operator is applied to arguments of the wrong sort
        {
            return true;
        }

        // Exclude crates that crash and also take longer than 2 minutes to analyze, or don't terminate
        if file_name.starts_with("client/faucet/src") // non termination
            || file_name.starts_with("config/management/operational/src") // crash
            || file_name.starts_with("consensus/src") // (ite (= 1 0) 1 (ite a!1 1 0))) at position 1 does not match declaration
            || file_name.starts_with("crypto/crypto-derive/src") // out of memory
            || file_name.starts_with("json-rpc/src") // expected a type, but found another kind
            || file_name.starts_with("execution/execution-correctness/src") // unreachable: checker/src/body_visitor.rs:1213:38
            || file_name.starts_with("language/compiler/src") // out of memory
            || file_name.starts_with("language/diem-framework/releases/src") // non termination
            || file_name.starts_with("language/diem-tools/df-cli/src") // out of memory
            || file_name.starts_with("language/diem-vm/src") // 'Not a type: DefIndex(3132)
            || file_name.starts_with("language/move-lang/src") // non termination
            || file_name.starts_with("language/move-model/src") // non termination
            || file_name.starts_with("language/tools/genesis-viewer/src/main.rs") // out of memory
            || file_name.starts_with("language/tools/move-bytecode-viewer/src") // out of memory
            || file_name.starts_with("language/tools/move-cli/src") // non termination
            || file_name.starts_with("language/tools/move-package/src") // expect reference target to have a value
            || file_name.starts_with("language/move-prover/src") // non termination
            || file_name.starts_with("language/move-prover/bytecode/src") // non termination
            || file_name.starts_with("language/move-prover/lab/src") // out of memory
            || file_name.starts_with("language/move-prover/mutation/src") // out of memory
            || file_name.starts_with("language/move-stdlib/src") // out of memory
            || file_name.starts_with("language/tools/move-unit-test/src") // non termination
            || file_name.starts_with("language/tools/read-write-set/src")  // non termination
            || file_name.starts_with("language/tools/vm-genesis/src") // Unexpected representation of upvar types
            || file_name.starts_with("mempool/src") // out of memory
            || file_name.starts_with("network/src")
            || file_name.starts_with("network/builder/src") // compiler/rustc_traits/src/normalize_erasing_regions.rs:54:32:
            || file_name.starts_with("sdk/client/src") // non termination
            || file_name.starts_with("state-sync/state-sync-v1/src") // Unexpected representation of upvar types
            || file_name.starts_with("storage/backup/backup-cli/src") // out of memory
            || file_name.starts_with("storage/diemdb/src") // expect reference target to have a value local_1(41) Some({result: &(local_1(41))})
            || file_name.starts_with("storage/diemsum/src") // out of memory
            || file_name.starts_with("storage/inspector/src/")
        // out of memory
        {
            return true;
        }

        // Conditionally exclude crates that currently slow down testing too much
        if self.options.diag_level == DiagLevel::Default
            && (file_name.starts_with("client/assets-proof/src")
                || file_name.starts_with("common/num-variants/src")
                || file_name.starts_with("common/rate-limiter/src")
                || file_name.starts_with("config/src")
                || file_name.starts_with("config/management/src")
                || file_name.starts_with("config/management/genesis/src")
                || file_name.starts_with("config/seed-peer-generator/src")
                || file_name.starts_with("common/debug-interface/src")
                || file_name.starts_with("crypto/crypto/src")
                || file_name.starts_with("execution/db-bootstrapper/src")
                || file_name.starts_with("execution/executor/src")
                || file_name.starts_with("json-rpc/types/src")
                || file_name.starts_with("language/bytecode-verifier/src")
                || file_name.starts_with("language/compiler/ir-to-bytecode/src")
                || file_name.starts_with("language/compiler/ir-to-bytecode/syntax/src")
                || file_name.starts_with("language/diem-tools/diem-validator-interface")
                || file_name.starts_with("language/diem-tools/writeset-transaction-generator/src")
                || file_name.starts_with("language/move-binary-format/src")
                || file_name.starts_with("language/move-core/types/src")
                || file_name.starts_with("language/move-prover/abigen/src")
                || file_name.starts_with("language/move-prover/boogie-backend-exp/src")
                || file_name.starts_with("language/move-prover/interpreter/src")
                || file_name.starts_with("language/move-prover/interpreter/crypto/src")
                || file_name.starts_with("language/tools/disassembler/src")
                || file_name.starts_with("move-prover/errmapgen/src")
                || file_name.starts_with("config/management/network-address-encryption/src")
                || file_name.starts_with("network/discovery/src")
                || file_name.starts_with("network/simple-onchain-discovery/src")
                || file_name.starts_with("consensus/safety-rules/src")
                || file_name.starts_with("sdk/src")
                || file_name.starts_with("secure/key-manager/src")
                || file_name.starts_with("secure/net/src")
                || file_name.starts_with("secure/storage/src")
                || file_name.starts_with("secure/storage/github/src")
                || file_name.starts_with("secure/storage/vault/src")
                || file_name.starts_with("state-sync/src")
                || file_name.starts_with("state-sync/inter-component/event-notifications/src")
                || file_name.starts_with("storage/storage-client/src")
                || file_name.starts_with("types/src")
                || file_name.starts_with("vm-validator/src"))
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
                if self.options.statistics {
                    println!("{}, not analyzed, 0", self.file_name);
                }
                return;
            }
        } else if self.is_excluded(&self.file_name) {
            if self.options.statistics {
                println!("{}, not analyzed, 0", self.file_name);
            }
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
        let call_graph_config = self.options.call_graph_config.to_owned();
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
            call_graph: CallGraph::new(call_graph_config),
        };
        crate_visitor.analyze_some_bodies();
        crate_visitor.call_graph.output();
    }
}
