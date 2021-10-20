// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a lazy static initializer

// MIRAI_FLAGS --diag=default

use core::ops::Deref;
use std::cell::{Cell, UnsafeCell};
use std::hint::unreachable_unchecked;
use std::marker::PhantomData;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Mutex;
use std::thread::{self, Thread};

const NB_BUCKETS: usize = 1 << 12; // 4096

type Bucket = Option<Box<Entry>>;

pub struct Entry {
    pub string: Box<str>,
    pub hash: u64,
    pub next: Bucket,
}

pub struct Pool(pub Box<[Bucket; NB_BUCKETS]>);

impl Pool {
    pub fn new() -> Self {
        let vec = std::mem::ManuallyDrop::new(vec![0_usize; NB_BUCKETS]);
        Self(unsafe { Box::from_raw(vec.as_ptr() as *mut [Bucket; NB_BUCKETS]) })
    }
}

pub struct Waiter {
    pub thread: Cell<Option<Thread>>,
    pub signaled: AtomicBool,
    pub next: *const Waiter,
}

pub struct WaiterQueue<'a> {
    pub state_and_queue: &'a AtomicUsize,
    pub set_state_on_drop_to: usize,
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

pub struct OnceCellS<T> {
    pub state_and_queue: AtomicUsize,
    pub _marker: PhantomData<*mut Waiter>,
    pub value: UnsafeCell<Option<T>>,
}

const INCOMPLETE: usize = 0x0;
const RUNNING: usize = 0x1;
const COMPLETE: usize = 0x2;
const STATE_MASK: usize = 0x3;

impl<T> OnceCellS<T> {
    pub const fn new() -> OnceCellS<T> {
        OnceCellS {
            state_and_queue: AtomicUsize::new(INCOMPLETE),
            _marker: PhantomData,
            value: UnsafeCell::new(None),
        }
    }

    pub unsafe fn get_unchecked(&self) -> &T {
        debug_assert!(self.is_initialized());
        let slot: &Option<T> = &*self.value.get();
        match slot {
            Some(value) => value,
            None => {
                debug_assert!(false);
                unreachable_unchecked()
            }
        }
    }

    pub fn initialize<F, E>(&self, f: F) -> Result<(), E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        let mut f = Some(f);
        let mut res: Result<(), E> = Ok(());
        let slot: *mut Option<T> = self.value.get();
        initialize_inner(&self.state_and_queue, &mut || {
            let f = unsafe { crate::take_unchecked(&mut f) };
            match f() {
                Ok(value) => {
                    unsafe { *slot = Some(value) };
                    true
                }
                Err(err) => {
                    res = Err(err);
                    false
                }
            }
        });
        res
    }

    pub fn is_initialized(&self) -> bool {
        self.state_and_queue.load(Ordering::Acquire) == COMPLETE
    }
}

fn initialize_inner(my_state_and_queue: &AtomicUsize, init: &mut dyn FnMut() -> bool) -> bool {
    let mut state_and_queue = my_state_and_queue.load(Ordering::Acquire);

    loop {
        match state_and_queue {
            COMPLETE => return true,
            INCOMPLETE => {
                let exchange = my_state_and_queue.compare_exchange(
                    state_and_queue,
                    RUNNING,
                    Ordering::Acquire,
                    Ordering::Acquire,
                );
                if let Err(old) = exchange {
                    state_and_queue = old;
                    continue;
                }
                let mut waiter_queue = WaiterQueue {
                    state_and_queue: my_state_and_queue,
                    set_state_on_drop_to: INCOMPLETE,
                };
                let success = init();

                waiter_queue.set_state_on_drop_to = if success { COMPLETE } else { INCOMPLETE };
                return success;
            }
            _ => {
                assert!(state_and_queue & STATE_MASK == RUNNING);
                wait(&my_state_and_queue, state_and_queue);
                state_and_queue = my_state_and_queue.load(Ordering::Acquire);
            }
        }
    }
}

fn wait(state_and_queue: &AtomicUsize, mut current_state: usize) {
    loop {
        if current_state & STATE_MASK != RUNNING {
            return;
        }

        let node = Waiter {
            thread: Cell::new(Some(thread::current())),
            signaled: AtomicBool::new(false),
            next: (current_state & !STATE_MASK) as *const Waiter,
        };
        let me = &node as *const Waiter as usize;

        let exchange = state_and_queue.compare_exchange(
            current_state,
            me | RUNNING,
            Ordering::Release,
            Ordering::Relaxed,
        );
        if let Err(old) = exchange {
            current_state = old;
            continue;
        }

        while !node.signaled.load(Ordering::Acquire) {
            thread::park();
        }
        break;
    }
}

unsafe fn take_unchecked<T>(val: &mut Option<T>) -> T {
    match val.take() {
        Some(it) => it,
        None => {
            debug_assert!(false);
            std::hint::unreachable_unchecked()
        }
    }
}

unsafe impl<T: Sync + Send> Sync for OnceCellS<T> {}
unsafe impl<T: Send> Send for OnceCellS<T> {}

pub struct OnceCell<T>(OnceCellS<T>);

impl<T> OnceCell<T> {
    /// Creates a new empty cell.
    pub const fn new() -> OnceCell<T> {
        OnceCell(OnceCellS::new())
    }

    pub fn get(&self) -> Option<&T> {
        if self.0.is_initialized() {
            Some(unsafe { self.get_unchecked() })
        } else {
            None
        }
    }

    pub unsafe fn get_unchecked(&self) -> &T {
        self.0.get_unchecked()
    }

    pub fn get_or_init<F>(&self, f: F) -> &T
    where
        F: FnOnce() -> T,
    {
        enum Void {}
        match self.get_or_try_init(|| Ok::<T, Void>(f())) {
            Ok(val) => val,
            Err(void) => match void {},
        }
    }

    pub fn get_or_try_init<F, E>(&self, f: F) -> Result<&T, E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        if let Some(value) = self.get() {
            return Ok(value);
        }
        self.0.initialize(f)?;

        debug_assert!(self.0.is_initialized());
        Ok(unsafe { self.get_unchecked() })
    }
}

pub struct Lazy<T, F = fn() -> T> {
    pub cell: OnceCell<T>,
    pub init: Cell<Option<F>>,
}

unsafe impl<T, F: Send> Sync for Lazy<T, F> where OnceCell<T>: Sync {}

impl<T, F> Lazy<T, F> {
    pub const fn new(f: F) -> Lazy<T, F> {
        Lazy {
            cell: OnceCell::new(),
            init: Cell::new(Some(f)),
        }
    }
}

impl<T, F: FnOnce() -> T> Lazy<T, F> {
    pub fn force(this: &Lazy<T, F>) -> &T {
        this.cell.get_or_init(|| match this.init.take() {
            Some(f) => f(),
            None => panic!("Lazy instance has previously been poisoned"),
        })
    }
}

impl<T, F: FnOnce() -> T> Deref for Lazy<T, F> {
    type Target = T;
    fn deref(&self) -> &T {
        Lazy::force(self)
    }
}

pub static SYMBOL_POOL: Lazy<Mutex<Pool>> = Lazy::new(|| Mutex::new(Pool::new()));

// pub fn t1() {
//     let _ = Lazy::force(&SYMBOL_POOL);
// }
//
// pub fn t2() {
//     let _ = SYMBOL_POOL.deref();
// }

pub fn main() {}
