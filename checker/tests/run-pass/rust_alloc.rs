// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses built-in contracts for the Vec struct.

use mirai_annotations::*;

use std::alloc::{alloc, dealloc, Layout};

pub fn test() {
    unsafe {
        let layout = Layout::new::<u16>();
        let ptr = alloc(layout);

        *(ptr as *mut u16) = 42;
        verify!(*(ptr as *mut u16) == 42);

        dealloc(ptr, layout);
    }
}

pub fn main() {}
