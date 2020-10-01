// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that std::usize::MAX is set correctly

use mirai_annotations::*;

#[cfg(any(
    target_arch = "x86",
    target_arch = "mips",
    target_arch = "mips",
    target_arch = "powerpc",
    target_arch = "arm"
))]
fn test() {
    verify!(std::usize::MAX == 4294967295);
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "powerpc64",
    target_arch = "aarch64"
))]
fn test() {
    verify!(std::usize::MAX == 18446744073709551615);
}

pub fn main() {
    test();
}
