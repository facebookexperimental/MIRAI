// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//
// A test that does unsafe casting and manipulation of pointers to transparent wrappers

// MIRAI_FLAGS --diag=verify

use std::cell::Cell;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::thread::Thread;

const RUNNING: usize = 0x1;
const STATE_MASK: usize = 0x3;

#[repr(align(4))] // Ensure the two lower bits are free to use as state bits.
pub struct Waiter {
    thread: Cell<Option<Thread>>,
    signaled: AtomicBool,
    next: *const Waiter,
}

pub struct WaiterQueue<'a> {
    state_and_queue: &'a AtomicUsize,
    set_state_on_drop_to: usize,
}

impl Drop for WaiterQueue<'_> {
    fn drop(&mut self) {
        let state_and_queue = self
            .state_and_queue
            .swap(self.set_state_on_drop_to, Ordering::AcqRel);

        assert_eq!(state_and_queue & STATE_MASK, RUNNING);

        unsafe {
            let mut queue = (state_and_queue & !STATE_MASK) as *const Waiter;
            while !queue.is_null() {
                let next = (*queue).next;
                let thread = (*queue).thread.replace(None).unwrap();
                (*queue).signaled.store(true, Ordering::Release);
                queue = next;
                thread.unpark();
            }
        }
    }
}

pub fn main() {}
