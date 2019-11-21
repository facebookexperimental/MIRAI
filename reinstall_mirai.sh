#!/bin/bash -v
#Copyright (c) Facebook, Inc. and its affiliates.

# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

# Use this script to update the seed summary store in mirai/binaries/summary_store.tar

# Exit immediately if a command exits with a non-zero status.
set -e

# start clean
cargo clean

#install mirai into cargo
cargo uninstall -q mirai || true
cargo install --path ./checker

