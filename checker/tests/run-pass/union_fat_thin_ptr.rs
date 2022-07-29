// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that a fat pointer can be tracked over a union with a thin pointer.

use mirai_annotations::*;
use std::mem::ManuallyDrop;

#[repr(C)]
pub union FatUnion<T> {
    pub thin: *const [T],
    pub fat: ManuallyDrop<FatPtr<T>>,
}

#[repr(C)]
pub struct FatPtr<T> {
    pub ptr: *const T,
    pub fat: usize,
}

pub const fn magic_mirror<T>(ptr: *const T, fat: usize) -> *const [T] {
    unsafe {
        FatUnion {
            fat: ManuallyDrop::new(FatPtr { ptr, fat }),
        }
        .thin
    }
}

pub fn main() {
    let arr_ref: &[i32] = &[1, 2, 3];
    let fat_is_thin = magic_mirror(arr_ref.as_ptr(), 3000);
    verify!(unsafe { &*fat_is_thin }[0] == 1);
    verify!(unsafe { &*fat_is_thin }[1] == 2);
    verify!(unsafe { &*fat_is_thin }[2] == 3);
    verify!(unsafe { &*fat_is_thin }.len() == 3000);
}
