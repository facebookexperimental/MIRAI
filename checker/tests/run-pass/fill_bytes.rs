// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A regression test that does a lot of heap stuff.

// MIRAI_FLAGS --diag=verify

#[cfg(not(windows))]
use std::cell::UnsafeCell;
#[cfg(not(windows))]
use std::rc::Rc;

#[cfg(not(windows))]
pub struct BlockRng {
    pub results: &'static [u32],
    pub index: usize,
}

#[cfg(not(windows))]
pub struct ThreadRng {
    rng: Rc<UnsafeCell<BlockRng>>,
}

#[cfg(not(windows))]
static A: [u32; 32] = [0; 32];

thread_local!(
    #[cfg(not(windows))]
    static THREAD_RNG_KEY: Rc<UnsafeCell<BlockRng>> = {
        let r = BlockRng { results: &A, index: 0 };
        Rc::new(UnsafeCell::new(r))
    }
);

#[cfg(not(windows))]
pub fn thread_rng() -> ThreadRng {
    let rng = THREAD_RNG_KEY.with(|t| t.clone());
    ThreadRng { rng }
}

#[cfg(not(windows))]
impl ThreadRng {
    pub fn fill_bytes(&mut self, dest: &mut [u8]) {
        use core::cmp::min;
        let rng = unsafe { &mut *self.rng.get() };
        let src = rng.results;
        const SIZE: usize = core::mem::size_of::<u32>();
        let _chunk_size_u8 = min(src.len() * SIZE, dest.len());
    }
}

#[cfg(not(windows))]
pub fn new_with_temp_dir() {
    // let mut rng = thread_rng();
    // let mut bytes = [0_u8; 16];
    // todo: fix this
    //rng.fill_bytes(&mut bytes);
}

pub fn main() {}
