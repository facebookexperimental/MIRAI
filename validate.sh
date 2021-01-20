#!/bin/bash -v
#Copyright (c) Facebook, Inc. and its affiliates.

# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

# Exit immediately if a command exits with a non-zero status.
set -e
# start clean
cargo clean
# Run format checks
cargo fmt --all
# Run lint checks
cargo audit
cargo clippy -- -D warnings
# Build
cd checker; cargo rustc --lib -- -D rust-2018-idioms
cd ..
cargo build

# build the mirai-standard-contracts crate
touch standard_contracts/src/lib.rs
RUSTFLAGS="-Z force-overflow-checks=off" RUSTC_WRAPPER=target/debug/mirai RUST_BACKTRACE=1 MIRAI_LOG=warn MIRAI_START_FRESH=true MIRAI_SHARE_PERSISTENT_STORE=true MIRAI_FlAGS="--diag=paranoid" cargo build --lib -p mirai-standard-contracts

# collect the summary store into a tar file
cd target/debug/deps
tar -c -f ../../../binaries/summary_store.tar .summary_store.sled
cd ../../..

# Run cargo test, starting clean so that the new summary store is used.
cargo clean
cargo build --tests
time cargo test

# Install MIRAI into cargo so that we can use optimized binaries to analyze debug binaries built with special flags
cargo uninstall mirai || true
cargo install --path ./checker

# Run mirai on itself (using the optimized build in cargo as the bootstrap).
cargo clean
RUSTFLAGS="-Z always_encode_mir" cargo build
touch checker/src/lib.rs
RUSTFLAGS="-Z always_encode_mir" RUSTC_WRAPPER=mirai RUST_BACKTRACE=full MIRAI_LOG=warn cargo build --lib -p mirai
