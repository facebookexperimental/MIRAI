#!/bin/bash -v
#Copyright (c) Facebook, Inc. and its affiliates.

# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

# Exit immediately if a command exits with a non-zero status.
set -e

# Check if dynamic link to vcpkg installed Z3 is wanted rather than static linking
if [ "$1" == "vcpkg" ]; then
  FLAGS='--no-default-features --features=vcpkg'
fi

# start clean
cargo clean
cargo update
# Run format checks
cargo fmt --all
# Run lint checks
cargo audit
cargo clippy --no-default-features --all-targets -- -D warnings
# Build mirai (in debug mode) so that we can build the standard contracts
cargo build --no-default-features

# build the mirai-standard-contracts crate
touch standard_contracts/src/lib.rs
cargo build --lib -p mirai-standard-contracts
touch standard_contracts/src/lib.rs
RUSTC_WRAPPER=target/debug/mirai RUST_BACKTRACE=1 MIRAI_LOG=warn MIRAI_START_FRESH=true MIRAI_SHARE_PERSISTENT_STORE=true MIRAI_FLAGS="--diag=paranoid" cargo build --lib -p mirai-standard-contracts

# collect the summary store into a tar file
cd target/debug/deps
tar -c -f ../../../binaries/summary_store.tar .summary_store.sled
cd ../../..

# Run cargo test, starting clean so that the new summary store is used.
cargo clean
cargo build --tests $FLAGS
time cargo test $FLAGS

# Install MIRAI into cargo so that we can use optimized binaries to analyze debug binaries built with special flags
cargo uninstall mirai || true
cargo install --path ./checker $FLAGS

# Run mirai on itself, using the optimized build in cargo as the bootstrap.
cargo clean -p mirai
cargo mirai --no-default-features
