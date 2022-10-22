// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// This tests de-referencing a vector inside a transparent wrapper

// use mirai_annotations::*;

#[repr(transparent)]
pub struct Buf {
    pub inner: Vec<u8>,
}

#[repr(transparent)]
pub struct Slice {
    pub inner: [u8],
}

impl Buf {
    pub fn as_slice(&self) -> &Slice {
        unsafe { std::mem::transmute(&*self.inner) }
    }
}

pub fn t1() {
    let b = Buf { inner: vec![10] };
    let _sl = b.as_slice();
    // todo: fix this
    // verify!(sl.inner.len() == 1);
}

pub fn main() {}
