#!/bin/bash
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
cargo install --path ./checker
# Run mirai on itself
rm -rf target/debug/deps/.summary_store.sled
touch checker/src/lib.rs
RUSTC_WRAPPER=mirai RUST_BACKTRACE=1 MIRAI_LOG=warn cargo check --lib -p mirai
