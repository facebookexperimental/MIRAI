// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that looks up collection element value via indices that have not been obviously written to.

#![stable(feature = "dummy", since = "1.0.0")]
#![feature(intrinsics, staged_api)]
#![feature(const_mut_refs, const_intrinsic_copy, const_ptr_offset)]

use mirai_annotations::*;

extern "rust-intrinsic" {
    #[rustc_const_unstable(feature = "const_intrinsic_copy", issue = "80697")]
    fn copy_nonoverlapping<T>(src: *const T, dst: *mut T, count: usize);
}

fn t1(b: &mut [i32; 3], n: usize) {
    let a = [1, 2, 3];
    unsafe {
        let aptr = a.as_ptr();
        let bptr = b.as_mut_ptr();
        copy_nonoverlapping(aptr, bptr, n);
    }
}

#[stable(feature = "dummy", since = "1.0.0")]
pub fn main() {
    let mut b = [0; 3];
    t1(&mut b, 2);
    verify!(b[0] == 1); //~ possible false verification condition
    verify!(b[2] == 0);
}
