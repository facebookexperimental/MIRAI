// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that causes two non empty states to join.

pub fn foo(flag: bool) -> i32 {
   if flag { 10 } else { 20 }
}
