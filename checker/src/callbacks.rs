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
        if file_name.contains("client/faucet/src") // too slow
            || file_name.contains("client/swiss-knife/src") // too slow 
            || file_name.contains("common/debug-interface/src") // !def.is_enum()
            || file_name.contains("common/logger/src") // !def.is_enum()
            || file_name.contains("common/logger/derive/src") // meta programming
            || file_name.contains("common/metrics/src") // too slow
            || file_name.contains("common/num-variants/src") // meta programming
            || file_name.contains("common/rate-limiter/src") // too slow
            || file_name.contains("common/time-service/src") // collections of call backs
            || file_name.contains("common/trace/src") // Sorts Int and <null> are incompatible
            || file_name.contains("config/src") // Sorts Int and <null> are incompatible
            || file_name.contains("config/seed-peer-generator/src") //  Sorts Int and <null> are incompatible
            || file_name.contains("config/management/src") // too slow
            || file_name.contains("config/management/genesis/src") // too slow    
            || file_name.contains("config/management/network-address-encryption/src") // Sorts Int and <null> are incompatible
            || file_name.contains("config/management/operational/src") // too slow
            || file_name.contains("consensus/src") // Sorts Int and <null> are incompatible 
            || file_name.contains("consensus/safety-rules/src") // Sorts Int and <null> are incompatible
            || file_name.contains("crypto/crypto-derive/src") // too much parsing
            || file_name.contains("diem-node/src") // Sorts Int and <null> are incompatible    
            || file_name.contains("execution/execution-correctness/src") // Sorts Int and <null> are incompatible
            || file_name.contains("json-rpc/src") // stack overflow
            || file_name.contains("language/bytecode-verifier/src") // too slow
            || file_name.contains("language/diem-tools/diem-events-fetcher/src") // resolve error
            || file_name.contains("language/compiler/src") // Sorts Int and Bool are incompatible
            || file_name.contains("language/compiler/ir-to-bytecode/src") // Sorts Int and Bool are incompatible
            || file_name.contains("language/compiler/ir-to-bytecode/syntax/src") // Sorts Int and Bool are incompatible
            || file_name.contains("language/diem-tools/transaction-replay/src")  // Not a type   
            || file_name.contains("language/diem-tools/writeset-transaction-generator/src") // stack overflow
            || file_name.contains("language/diem-framework/src") // too slow    
            || file_name.contains("language/move-lang/src") // too slow
            || file_name.contains("language/move-model/src") // too slow
            || file_name.contains("language/move-prover/src") // too slow 
            || file_name.contains("language/move-prover/boogie-backend/src") // index out of bounds
            || file_name.contains("language/move-prover/docgen/src") // too slow
            || file_name.contains("language/move-prover/bytecode/src") // too slow 
            || file_name.contains("language/tools/move-bytecode-viewer/src") // too slow
            || file_name.contains("language/tools/move-cli/src") // too slow
            || file_name.contains("language/tools/move-coverage/src") // too slow
            || file_name.contains("language/tools/vm-genesis/src") // too slow
            || file_name.contains("language/transaction-builder/generator/src") // too slow
            || file_name.contains("language/vm/src") // too slow
            || file_name.contains("mempool/src") //  !def.is_enum()
            || file_name.contains("network/src") // too slow
            || file_name.contains("network/builder/src") // Sorts Int and <null> are incompatible
            || file_name.contains("network/simple-onchain-discovery/src") // Sorts Int and <null> are incompatible   
            || file_name.contains("sdk/client/src") // Sorts <null> and Int are incompatible
            || file_name.contains("secure/key-manager/src") // too slow   
            || file_name.contains("secure/storage/github/src") // !def.is_enum()
            || file_name.contains("secure/net/src") // too slow
            || file_name.contains("secure/storage/vault/src") // Sorts Int and <null> are incompatible
            || file_name.contains("state-sync/src") // Sorts <null> and Int are incompatible
            || file_name.contains("secure/storage/src") // !def.is_enum()
            || file_name.contains("storage/backup/backup-cli/src") // unreachable code
            || file_name.contains("storage/diemdb/src") // stack overflow
            || file_name.contains("storage/schemadb/src") // too slow
            || file_name.contains("storage/storage-client/src") // too slow
            || file_name.contains("types/src")
        {
            return true;
        }

        if self.options.diag_level == DiagLevel::Paranoid {
            return file_name.contains("client/faucet/src") // stack overflow
                    || file_name.contains("common/debug-interface/src") // stack overflow 
                    || file_name.contains("common/logger/src") // operator is applied to arguments of the wrong sort
                    || file_name.contains("common/logger/derive/src") // too slow
                    || file_name.contains("common/metrics/src") // not implemented: replacing embedded path root     
                    || file_name.contains("common/num-variants/src") // too slow    
                    || file_name.contains("common/proptest-helpers/src") // checker/src/body_visitor.rs:1196:38 
                    || file_name.contains("common/rate-limiter/src") // too slow
                    || file_name.contains("common/trace/src") // stack overflow
                    || file_name.contains("config/src") // stack overflow
                    || file_name.contains("config/seed-peer-generator/src") // stack overflow    
                    || file_name.contains("config/management/network-address-encryption/src") // stack overflow    
                    || file_name.contains("consensus/src") // too slow    
                    || file_name.contains("consensus/safety-rules/src") // too slow    
                    || file_name.contains("crypto/crypto-derive/src") // too slow 
                    || file_name.contains("diem-node/src") // stack overflow    
                    || file_name.contains("execution/execution-correctness/src") // stack overflow
                    || file_name.contains("language/compiler/src") // Sorts Int and Bool are incompatible
                    || file_name.contains("language/compiler/ir-to-bytecode/src") // Sorts Int and Bool are incompatible
                    || file_name.contains("language/compiler/ir-to-bytecode/syntax/src") // Sorts Bool and Int are incompatible
                    || file_name.contains("language/diem-vm/src") // Not a type     
                    || file_name.contains("language/diem-framework/src") // too slow    
                    || file_name.contains("language/diem-tools/diem-events-fetcher/src") // stack overflow
                    || file_name.contains("language/diem-tools/writeset-transaction-generator/src") // stack overflow
                    || file_name.contains("language/diem-tools/transaction-replay/src")  // Not a type   
                    || file_name.contains("language/move-prover/src") // too slow    
                    || file_name.contains("language/move-prover/boogie-backend/src") // stack overflow    
                    || file_name.contains("language/move-prover/docgen/src") // too slow
                    || file_name.contains("language/tools/genesis-viewer/src") // too slow    
                    || file_name.contains("language/tools/move-bytecode-viewer/src") // too slow    
                    || file_name.contains("language/tools/move-cli/src") // too slow    
                    || file_name.contains("language/tools/vm-genesis/src") // too slow    
                    || file_name.contains("language/transaction-builder/generator/src") // not implemented: replacing embedded path root      
                    || file_name.contains("mempool/src") // too slow
                    || file_name.contains("network/src") // too slow
                    || file_name.contains("network/builder/src") // stack overflow     
                    || file_name.contains("network/simple-onchain-discovery/src") // stack overflow    
                    || file_name.contains("sdk/client/src") // Sorts <null> and Int are incompatible    
                    || file_name.contains("secure/net/src") // too slow
                    || file_name.contains("secure/key-manager/src") // stack overflow   
                    || file_name.contains("secure/storage/src") // stack overflow    
                    || file_name.contains("secure/storage/github/src") // thread 'rustc' has overflowed its stack
                    || file_name.contains("secure/storage/vault/src") // stack overflow
                    || file_name.contains("state-sync/src") // too slow    
                    || file_name.contains("storage/backup/backup-cli/src") // stack overflow    
                    || file_name.contains("storage/backup/backup-service/src") // stack overflow    
                    || file_name.contains("storage/diemdb/src") // stack overflow    
                    || file_name.contains("storage/schemadb/src") // stack overflow 
                    || file_name.contains("storage/storage-client/src"); // too slow
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
