// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that std::u16::MAX is set correctly

use mirai_annotations::*;

pub fn main() {
    verify!(std::u16::MAX == 65535);
}
