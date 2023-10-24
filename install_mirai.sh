#!/bin/bash -v
#Copyright (c) Facebook, Inc. and its affiliates.

# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

# Use this script to install a new version of MIRAI into cargo.

# Exit immediately if a command exits with a non-zero status.
set -e

#install mirai into cargo
cargo uninstall -q mirai || true
touch checker/src/lib.rs

# Check if dynamic link to vcpkg installed Z3 is wanted rather than static linking
if [ "$1" == "vcpkg" ]; then
  cargo install --locked --path ./checker --no-default-features --features=vcpkg
else
  cargo install --locked --path ./checker
fi

