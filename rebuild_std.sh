#!/bin/bash
#Copyright (c) Facebook, Inc. and its affiliates.

# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

# Use this script to update the seed summary store in mirai/binaries/summary_store.tar

# Exit immediately if a command exits with a non-zero status.
set -e

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