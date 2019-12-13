#!/bin/bash -v
#Copyright (c) Facebook, Inc. and its affiliates.

# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

# Exit immediately if a command exits with a non-zero status.
set -e
# start clean
cargo clean -p mirai
# Run format checks
cargo fmt --all
# Run lint checks
cargo audit
cargo clippy -- -D warnings
# Build
cd checker; cargo rustc --lib -- -D rust-2018-idioms
cd ..; cargo build

# Install MIRAI into cargo
cargo uninstall mirai || true
cargo install --debug --path ./checker

# build the mirai-standard-contracts crate
touch standard_contracts/src/lib.rs
RUSTFLAGS="-Z force-overflow-checks=off" RUSTC_WRAPPER=mirai RUST_BACKTRACE=1 MIRAI_LOG=warn MIRAI_START_FRESH=true MIRAI_SHARE_PERSISTENT_STORE=true cargo build --lib -p mirai-standard-contracts

# collect the summary store into a tar file
cd target/debug/deps
tar -c -f ../../../binaries/summary_store.tar .summary_store.sled
cd ../../..

# Install MIRAI into cargo again, so that this time it uses the new sumary store
cargo uninstall mirai || true
cargo install --path ./checker

# Run cargo test
cargo build
cargo test

# Run mirai on itself
cargo clean
RUSTFLAGS="-Z always_encode_mir" cargo build
touch checker/src/lib.rs
RUSTFLAGS="-Z always_encode_mir" RUSTC_WRAPPER=mirai RUST_BACKTRACE=1 MIRAI_LOG=warn cargo build --lib -p mirai
