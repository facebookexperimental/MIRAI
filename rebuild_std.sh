#!/bin/bash -v
#Copyright (c) Facebook, Inc. and its affiliates.

# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

# Use this script to update the seed summary store in mirai/binaries/summary_store.tar

# start clean
cargo clean

#install mirai into cargo (use --debug because it is quicker to build and build is currently the long pole)
cargo uninstall -q mirai || true
cargo install --debug --path ./checker

# build the mirai-standard-contracts crate
touch standard_contracts/src/lib.rs
RUSTC_WRAPPER=mirai RUST_BACKTRACE=1 MIRAI_LOG=warn MIRAI_START_FRESH=true cargo build --lib -p mirai-standard-contracts

# collect the summary store into a tar file
cd target/debug/deps
tar -c -f ../../../binaries/summary_store.tar .summary_store.sled
cd ../../..

# rebuild mirai
cargo build
cargo uninstall mirai
cargo install --path ./checker

