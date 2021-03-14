// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks relaxed mode preconditions

// MIRAI_FLAGS --diag=default

use mirai_annotations::*;

fn foo(i: i32) {
    precondition!(i > 3); //~ related location
}

pub fn bar(i: i32) {
    // No diagnostic here since default mode silently promotes the precondition even though
    // bar is an analysis root
    foo(i);
}

pub fn main() {
    // Diagnostic here since the unsatisfied precondition does not depend on a parameter
    // of the analysis root.
    foo(1); //~ unsatisfied precondition
}
