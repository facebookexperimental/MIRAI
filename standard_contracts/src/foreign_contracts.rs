// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(unknown_lints)]
#![allow(unused)]
#![allow(clippy::all)]

pub mod alloc {
    pub mod alloc {
        pub fn box_free() {}

        pub fn handle_alloc_error() {
            // Not something that can be reasonably detected with static analysis, so ignore.
        }

        pub fn __rust_dealloc() {}
    }

    pub mod collections {
        pub mod vec_deque {
            pub const INITIAL_CAPACITY: usize = 7; // 2^3 - 1
            pub const MINIMUM_CAPACITY: usize = 1; // 2 - 1
            #[cfg(target_pointer_width = "16")]
            pub const MAXIMUM_ZST_CAPACITY: usize = 1 << (16 - 1); // Largest possible power of two
            #[cfg(target_pointer_width = "32")]
            pub const MAXIMUM_ZST_CAPACITY: usize = 1 << (32 - 1); // Largest possible power of two
            #[cfg(target_pointer_width = "64")]
            pub const MAXIMUM_ZST_CAPACITY: usize = 1 << (64 - 1); // Largest possible power of two

            pub struct VecDeque<T> {
                _phantom: std::marker::PhantomData<T>,
                capacity: usize,
                len: usize,
            }

            pub mod implement_vec_deque {
                use crate::foreign_contracts::alloc::collections::vec_deque::VecDeque;

                pub fn new<T>() -> VecDeque<T> {
                    VecDeque {
                        _phantom: std::marker::PhantomData,
                        capacity: 0,
                        len: 0,
                    }
                }

                pub fn len<T>(_self: &VecDeque<T>) -> usize {
                    _self.len
                }

                pub fn is_empty<T>(_self: &VecDeque<T>) -> bool {
                    _self.len == 0
                }

                pub fn pop_front<T>(_self: &mut VecDeque<T>) -> Option<T> {
                    if _self.len == 0 {
                        None
                    } else {
                        _self.len -= 1;
                        result!()
                    }
                }

                pub fn pop_back<T>(_self: &mut VecDeque<T>) -> Option<T> {
                    if _self.len == 0 {
                        None
                    } else {
                        _self.len -= 1;
                        result!()
                    }
                }

                pub fn push_front<T>(_self: &mut VecDeque<T>, _value: T) {
                    assume!(_self.len < usize::max_value());
                    _self.len += 1;
                }

                pub fn push_back<T>(_self: &mut VecDeque<T>, _value: T) {
                    assume!(_self.len < usize::max_value());
                    _self.len += 1;
                }

                pub fn contains<T>(_self: &VecDeque<T>, _value: T) -> bool {
                    result!()
                }
            }
        }
    }

    pub mod fmt {
        pub fn format() -> String {
            result!()
        }
    }

    pub mod raw_vec {
        pub fn capacity_overflow() {}
    }

    pub mod rc {
        pub mod implement_rc {
            pub fn hash<T, H>(_self: T, state: &mut H) {
                result!()
            }
        }
    }
}

pub mod core {
    pub mod alloc {
        pub mod AllocRef {
            pub fn alloc(
                _self: &mut dyn std::alloc::AllocRef,
                _layout: std::alloc::Layout,
            ) -> Result<std::ptr::NonNull<u8>, core::alloc::AllocErr> {
                result!()
            }

            pub fn dealloc() {}
        }

        pub mod raw_vec {
            pub fn capacity_overflow() {
                assume_unreachable!("capacity overflow");
            }
        }
    }

    pub mod clone {
        pub mod Clone {
            pub fn clone<T>() -> T {
                result!()
            }
        }
    }

    pub mod cmp {
        pub fn max__i8(v1: i8, v2: i8) -> i8 {
            if v1 >= v2 {
                return v1;
            }
            return v2;
        }

        pub fn max__i16(v1: i16, v2: i16) -> i16 {
            if v1 >= v2 {
                return v1;
            }
            return v2;
        }

        pub fn max__i32(v1: i32, v2: i32) -> i32 {
            if v1 >= v2 {
                return v1;
            }
            return v2;
        }

        pub fn max__i64(v1: i64, v2: i64) -> i64 {
            if v1 >= v2 {
                return v1;
            }
            return v2;
        }

        pub fn max__i128(v1: i128, v2: i128) -> i128 {
            if v1 >= v2 {
                return v1;
            }
            return v2;
        }

        pub fn max__isize(v1: isize, v2: isize) -> isize {
            if v1 >= v2 {
                return v1;
            }
            return v2;
        }

        pub fn max__u8(v1: u8, v2: u8) -> u8 {
            if v1 >= v2 {
                return v1;
            }
            return v2;
        }

        pub fn max__u16(v1: u16, v2: u16) -> u16 {
            if v1 >= v2 {
                return v1;
            }
            return v2;
        }

        pub fn max__u32(v1: u32, v2: u32) -> u32 {
            if v1 >= v2 {
                return v1;
            }
            return v2;
        }

        pub fn max__u64(v1: u64, v2: u64) -> u64 {
            if v1 >= v2 {
                return v1;
            }
            return v2;
        }

        pub fn max__u128(v1: u128, v2: u128) -> u128 {
            if v1 >= v2 {
                return v1;
            }
            return v2;
        }

        pub fn max__usize(v1: usize, v2: usize) -> usize {
            if v1 >= v2 {
                return v1;
            }
            return v2;
        }

        pub trait Ord {
            fn cmp__usize(a: usize, b: usize) -> std::cmp::Ordering {
                if a < b {
                    std::cmp::Ordering::Less
                } else if a == b {
                    std::cmp::Ordering::Equal
                } else {
                    std::cmp::Ordering::Greater
                }
            }
        }

        pub trait PartialOrd<Rhs: ?Sized = Self> {
            fn lt__ref_i32_ref_i32(x: &i32, y: &i32) -> bool {
                (*x) < (*y)
            }
        }
    }

    pub mod convert {
        pub mod implement_convert {
            pub fn try_into__ref_slice_u8_array_u8(arg: &[u8]) -> &[u8] {
                arg
            }
        }
    }

    pub mod core_arch {
        pub mod x86 {
            pub mod sse2 {
                pub fn pause() {}
            }
        }
    }

    pub mod default {
        pub trait Default {
            fn default__T() {
                result!()
            }
        }
    }

    pub mod fmt {
        use std::marker::PhantomData;

        pub struct Arguments<'a> {
            phantom: PhantomData<&'a str>,
        }

        pub mod implement_core_fmt_Arguments {
            use crate::foreign_contracts::core::fmt::ArgumentV1;
            use crate::foreign_contracts::core::fmt::Arguments;

            pub fn new_v1<'a>(
                _pieces: &'a [&'a str],
                _args: &'a [ArgumentV1<'a>],
            ) -> Arguments<'a> {
                result!()
            }
        }

        pub struct ArgumentV1<'a> {
            phantom: PhantomData<&'a str>,
        }

        pub mod implement_core_fmt_ArgumentV1 {
            use crate::foreign_contracts::core::fmt::ArgumentV1;
            use crate::foreign_contracts::core::fmt::Formatter;
            use crate::foreign_contracts::core::fmt::Result;

            pub fn new<'b, T>(
                _x: &'b T,
                _f: fn(&T, &mut Formatter<'_>) -> Result,
            ) -> ArgumentV1<'b> {
                result!()
            }
        }

        pub struct Formatter<'a> {
            phantom: PhantomData<&'a str>,
        }

        pub struct Result {}

        pub mod rt {
            pub mod v1 {
                pub struct Argument {}
            }
        }

        pub struct Void {}
    }

    pub mod hash {
        pub mod Hasher {
            fn finish() {
                panic!("use StableHasher::finalize instead");
            }

            pub fn write<T>(_self: &mut T, _bytes: &[u8]) {
                // todo: provide non default models for interesting types
            }
        }
    }

    pub mod intrinsics {
        pub fn atomic_cxchg<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            result!()
        }
        pub fn atomic_cxchg_acq<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            result!()
        }
        pub fn atomic_cxchg_rel<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            result!()
        }
        pub fn atomic_cxchg_acqrel<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            result!()
        }
        pub fn atomic_cxchg_relaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            result!()
        }
        pub fn atomic_cxchg_failrelaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            result!()
        }
        pub fn atomic_cxchg_failacq<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            result!()
        }
        pub fn atomic_cxchg_acq_failrelaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            result!()
        }
        pub fn atomic_cxchg_acqrel_failrelaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            result!()
        }
        pub fn atomic_cxchgweak<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            result!()
        }
        pub fn atomic_cxchgweak_acq<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            result!()
        }
        pub fn atomic_cxchgweak_rel<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            result!()
        }
        pub fn atomic_cxchgweak_acqrel<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            result!()
        }
        pub fn atomic_cxchgweak_relaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            result!()
        }
        pub fn atomic_cxchgweak_failrelaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            result!()
        }
        pub fn atomic_cxchgweak_failacq<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            result!()
        }
        pub fn atomic_cxchgweak_acq_failrelaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            result!()
        }
        pub fn atomic_cxchgweak_acqrel_failrelaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            result!()
        }
        pub fn atomic_load<T>(src: *const T) -> T {
            result!()
        }
        pub fn atomic_load_acq<T>(src: *const T) -> T {
            result!()
        }
        pub fn atomic_load_relaxed<T>(src: *const T) -> T {
            result!()
        }
        pub fn atomic_load_unordered<T>(src: *const T) -> T {
            result!()
        }
        pub fn atomic_store<T>(dst: *mut T, val: T) {}
        pub fn atomic_store_rel<T>(dst: *mut T, val: T) {}
        pub fn atomic_store_relaxed<T>(dst: *mut T, val: T) {}
        pub fn atomic_store_unordered<T>(dst: *mut T, val: T) {}
        pub fn atomic_xchg<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_xchg_acq<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_xchg_rel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_xchg_acqrel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_xchg_relaxed<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_xadd<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_xadd_acq<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_xadd_rel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_xadd_acqrel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_xadd_relaxed<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_xsub<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_xsub_acq<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_xsub_rel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_xsub_acqrel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_xsub_relaxed<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_and<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_and_acq<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_and_rel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_and_acqrel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_and_relaxed<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_nand<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_nand_acq<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_nand_rel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_nand_acqrel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_nand_relaxed<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_or<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_or_acq<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_or_rel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_or_acqrel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_or_relaxed<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_xor<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_xor_acq<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_xor_rel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_xor_acqrel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_xor_relaxed<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_max<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_max_acq<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_max_rel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_max_acqrel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_max_relaxed<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_min<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_min_acq<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_min_rel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_min_acqrel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_min_relaxed<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_umin<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_umin_acq<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_umin_rel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_umin_acqrel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_umin_relaxed<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_umax<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_umax_acq<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_umax_rel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_umax_acqrel<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn atomic_umax_relaxed<T>(dst: *mut T, src: T) -> T {
            result!()
        }
        pub fn copy_nonoverlapping<T>() {}
        pub fn prefetch_read_data<T>(data: *const T, locality: i32) {}
        pub fn prefetch_write_data<T>(data: *const T, locality: i32) {}
        pub fn prefetch_read_instruction<T>(data: *const T, locality: i32) {}
        pub fn prefetch_write_instruction<T>(data: *const T, locality: i32) {}
        pub fn write_bytes<T>(_dst: *mut T, _val: u8, _count: usize) {}

        pub mod _1 {
            pub fn atomic_fence() {}
            pub fn atomic_fence_acq() {}
            pub fn atomic_fence_rel() {}
            pub fn atomic_fence_acqrel() {}
            pub fn atomic_singlethreadfence() {}
            pub fn atomic_singlethreadfence_acq() {}
            pub fn atomic_singlethreadfence_rel() {}
            pub fn atomic_singlethreadfence_acqrel() {}
            pub fn rustc_peek<T>(_: T) -> T {
                result!()
            }
            pub fn abort() {}
            pub fn unreachable() {}
            pub fn assume(b: bool) {
                assumed_postcondition!(b)
            }
            pub fn likely(b: bool) -> bool {
                result!()
            }
            pub fn unlikely(b: bool) -> bool {
                result!()
            }
            pub fn breakpoint() {}
            pub fn move_val_init<T>(dst: *mut T, src: T) {}
            pub fn min_align_of<T>() -> usize {
                4
            }
            pub fn pref_align_of<T>() -> usize {
                result!()
            }
            pub fn size_of_val<T: ?Sized>(_: &T) -> usize {
                result!()
            }
            pub fn min_align_of_val<T: ?Sized>(_: &T) -> usize {
                result!()
            }
            pub fn type_name<T: ?Sized>() -> &'static str {
                result!()
            }
            pub fn type_id<T: ?Sized + 'static>() -> u64 {
                result!()
            }
            pub fn panic_if_uninhabited<T>() {}
            pub fn caller_location<T>() -> T {
                result!()
            }
            pub fn init<T>() -> T {
                result!()
            }
            pub fn uninit<T>() -> T {
                result!()
            }
            pub fn forget<T>(_: T) {}
            pub fn transmute<T, U>(e: T) -> U {
                result!()
            }
            pub fn needs_drop<T>() -> bool {
                result!()
            }
            pub fn offset<T>(dst: *const T, offset: isize) -> *const T {
                result!()
            }
            pub fn arith_offset<T>(dst: *const T, offset: isize) -> *const T {
                result!()
            }
            pub fn volatile_copy_nonoverlapping_memory<T>(
                dst: *mut T,
                src: *const T,
                count: usize,
            ) {
            }
            pub fn volatile_copy_memory<T>(dst: *mut T, src: *const T, count: usize) {}
            pub fn volatile_set_memory<T>(dst: *mut T, val: u8, count: usize) {}
            pub fn volatile_load<T>(src: *const T) -> T {
                result!()
            }
            pub fn volatile_store<T>(dst: *mut T, val: T) {}
            pub fn unaligned_volatile_load<T>(src: *const T) -> T {
                result!()
            }
            pub fn unaligned_volatile_store<T>(dst: *mut T, val: T) {}
            pub fn sqrtf32(x: f32) -> f32 {
                result!()
            }
            pub fn sqrtf64(x: f64) -> f64 {
                result!()
            }
            pub fn powif32(a: f32, x: i32) -> f32 {
                result!()
            }
            pub fn powif64(a: f64, x: i32) -> f64 {
                result!()
            }
            pub fn sinf32(x: f32) -> f32 {
                result!()
            }
            pub fn sinf64(x: f64) -> f64 {
                result!()
            }
            pub fn cosf32(x: f32) -> f32 {
                result!()
            }
            pub fn cosf64(x: f64) -> f64 {
                result!()
            }
            pub fn powf32(a: f32, x: f32) -> f32 {
                result!()
            }
            pub fn powf64(a: f64, x: f64) -> f64 {
                result!()
            }
            pub fn expf32(x: f32) -> f32 {
                result!()
            }
            pub fn expf64(x: f64) -> f64 {
                result!()
            }
            pub fn exp2f32(x: f32) -> f32 {
                result!()
            }
            pub fn exp2f64(x: f64) -> f64 {
                result!()
            }
            pub fn logf32(x: f32) -> f32 {
                result!()
            }
            pub fn logf64(x: f64) -> f64 {
                result!()
            }
            pub fn log10f32(x: f32) -> f32 {
                result!()
            }
            pub fn log10f64(x: f64) -> f64 {
                result!()
            }
            pub fn log2f32(x: f32) -> f32 {
                result!()
            }
            pub fn log2f64(x: f64) -> f64 {
                result!()
            }
            pub fn fmaf32(a: f32, b: f32, c: f32) -> f32 {
                result!()
            }
            pub fn fmaf64(a: f64, b: f64, c: f64) -> f64 {
                result!()
            }
            pub fn fabsf32(x: f32) -> f32 {
                result!()
            }
            pub fn fabsf64(x: f64) -> f64 {
                result!()
            }
            pub fn minnumf32(x: f32, y: f32) -> f32 {
                result!()
            }
            pub fn minnumf64(x: f64, y: f64) -> f64 {
                result!()
            }
            pub fn maxnumf32(x: f32, y: f32) -> f32 {
                result!()
            }
            pub fn maxnumf64(x: f64, y: f64) -> f64 {
                result!()
            }
            pub fn copysignf32(x: f32, y: f32) -> f32 {
                result!()
            }
            pub fn copysignf64(x: f64, y: f64) -> f64 {
                result!()
            }
            pub fn floorf32(x: f32) -> f32 {
                result!()
            }
            pub fn floorf64(x: f64) -> f64 {
                result!()
            }
            pub fn ceilf32(x: f32) -> f32 {
                result!()
            }
            pub fn ceilf64(x: f64) -> f64 {
                result!()
            }
            pub fn truncf32(x: f32) -> f32 {
                result!()
            }
            pub fn truncf64(x: f64) -> f64 {
                result!()
            }
            pub fn rintf32(x: f32) -> f32 {
                result!()
            }
            pub fn rintf64(x: f64) -> f64 {
                result!()
            }
            pub fn nearbyintf32(x: f32) -> f32 {
                result!()
            }
            pub fn nearbyintf64(x: f64) -> f64 {
                result!()
            }
            pub fn roundf32(x: f32) -> f32 {
                result!()
            }
            pub fn roundf64(x: f64) -> f64 {
                result!()
            }
            pub fn fadd_fast<T>(a: T, b: T) -> T {
                result!()
            }
            pub fn fsub_fast<T>(a: T, b: T) -> T {
                result!()
            }
            pub fn fmul_fast<T>(a: T, b: T) -> T {
                result!()
            }
            pub fn fdiv_fast<T>(a: T, b: T) -> T {
                result!()
            }
            pub fn frem_fast<T>(a: T, b: T) -> T {
                result!()
            }
            pub fn ctlz<T>(x: T) -> T {
                result!()
            }
            pub fn ctlz_nonzero<T>(x: T) -> T {
                result!()
            }
            pub fn cttz<T>(x: T) -> T {
                result!()
            }
            pub fn cttz_nonzero<T>(x: T) -> T {
                result!()
            }
            pub fn bswap<T>(x: T) -> T {
                result!()
            }
            pub fn bitreverse<T>(x: T) -> T {
                result!()
            }

            pub fn add_with_overflow<T>(x: T, y: T) -> (T, bool) {
                result!()
            }
            pub fn add_with_overflow__usize(x: usize, y: usize) -> (u128, bool) {
                let result = (x as u128) + (y as u128);
                (
                    result % ((std::usize::MAX as u128) + 1),
                    result > (std::usize::MAX as u128),
                )
            }

            pub fn sub_with_overflow<T>(x: T, y: T) -> (T, bool) {
                result!()
            }
            pub fn sub_with_overflow__usize(x: usize, y: usize) -> (usize, bool) {
                let result = (x as i128) + (-(y as i128));
                (
                    (result % ((std::usize::MAX as i128) + 1)) as usize,
                    result < 0 || result > (std::usize::MAX as i128),
                )
            }

            /// Performs an exact division, resulting in undefined behavior when
            /// `x % y != 0` or `y == 0` or `x == T::min_value() && y == -1`
            pub fn exact_div<T>(x: T, y: T) -> T {
                result!()
            }
            pub fn exact_div__usize(x: usize, y: usize) -> usize {
                precondition!(y != 0);
                precondition!(x % y == 0);
                x / y
            }

            // These operations assume that no overflow/underflow will occur.
            // This is not checked at runtime, but code generation can proceed
            // on the assumption that there will be no overflow/underflow.

            pub fn unchecked_div<T>(x: T, y: T) -> T {
                result!()
            }
            pub fn unchecked_div__usize(x: usize, y: usize) -> usize {
                precondition!(y != 0);
                x * y
            }

            pub fn unchecked_rem<T>(x: T, y: T) -> T {
                result!()
            }
            pub fn unchecked_rem__usize(x: usize, y: usize) -> usize {
                precondition!(y != 0);
                x % y
            }

            pub fn unchecked_shl<T>(x: T, y: T) -> T {
                result!()
            }
            pub fn unchecked_shl__usize(x: usize, y: usize) -> usize {
                //precondition!(y <= crate::foreign_contracts::core::mem::size_of__usize());
                x << y
            }

            pub fn unchecked_shr<T>(x: T, y: T) -> T {
                result!()
            }
            pub fn unchecked_shr__usize(x: usize, y: usize) -> usize {
                //precondition!(y <= crate::foreign_contracts::core::mem::size_of__usize());
                x >> y
            }

            pub fn unchecked_add<T>(x: T, y: T) -> T {
                result!()
            }
            pub fn unchecked_add__usize(x: usize, y: usize) -> usize {
                precondition!((x as u128) + (y as u128) <= (std::usize::MAX as u128));
                x + y
            }

            pub fn unchecked_sub<T>(x: T, y: T) -> T {
                result!()
            }
            pub fn unchecked_sub__usize(x: usize, y: usize) -> usize {
                precondition!(x >= y);
                x - y
            }

            pub fn unchecked_mul<T>(x: T, y: T) -> T {
                result!()
            }
            pub fn unchecked_mul__usize(x: usize, y: usize) -> usize {
                precondition!((x as u128) * (y as u128) <= (std::usize::MAX as u128));
                x * y
            }

            // rotate_left: (X << (S % BW)) | (X >> ((BW - S) % BW))
            pub fn rotate_left<T>(x: T, y: T) -> T {
                result!()
            }
            pub fn rotate_left__usize(x: usize, y: usize) -> usize {
                let bw = crate::foreign_contracts::core::mem::size_of__usize();
                (x << (y % bw)) | (x >> ((bw - y) % bw))
            }

            // rotate_right: (X << ((BW - S) % BW)) | (X >> (S % BW))
            pub fn rotate_right<T>(x: T, y: T) -> T {
                result!()
            }
            pub fn rotate_right__usize(x: usize, y: usize) -> usize {
                let bw = crate::foreign_contracts::core::mem::size_of__usize();
                (x << ((bw - y) % bw)) | (x >> (y % bw))
            }

            // Wrapping operations are just the normal CPU ops with no extra runtime checks.
            // Code generation following such operations have to take into account the possibility
            // of overflow.

            /// (a + b) mod 2<sup>N</sup>, where N is the width of T
            pub fn wrapping_add<T>(a: T, b: T) -> T {
                result!()
            }
            pub fn wrapping_add__usize(a: usize, b: usize) -> u128 {
                ((a as u128) + (b as u128)) % ((std::usize::MAX as u128) + 1)
            }

            /// (a - b) mod 2 ** N, where N is the width of T in bits.
            pub fn wrapping_sub<T>(a: T, b: T) -> T {
                result!()
            }
            pub fn wrapping_sub__usize(a: usize, b: usize) -> usize {
                (((a as i128) + (-(b as i128))) % ((std::usize::MAX as i128) + 1)) as usize
            }

            /// (a * b) mod 2 ** N, where N is the width of T in bits.
            pub fn wrapping_mul<T>(a: T, b: T) -> T {
                result!()
            }
            pub fn wrapping_mul__usize(a: usize, b: usize) -> u128 {
                ((a as u128) * (b as u128)) % ((std::usize::MAX as u128) + 1)
            }

            pub fn saturating_add<T>(a: T, b: T) -> T {
                result!()
            }
            pub fn saturating_add__usize(a: usize, b: usize) -> usize {
                let result = (a as u128) + (b as u128);
                if result > (std::usize::MAX as u128) {
                    std::usize::MAX
                } else {
                    result as usize
                }
            }

            pub fn saturating_sub<T>(a: T, b: T) -> T {
                result!()
            }
            pub fn saturating_sub__usize(a: usize, b: usize) -> usize {
                if a < b {
                    0
                } else {
                    a - b
                }
            }

            pub fn discriminant_value<T>(v: &T) -> u64 {
                result!()
            }
            pub fn r#try(f: fn(*mut u8), data: *mut u8, local_ptr: *mut u8) -> i32 {
                result!()
            }
            pub fn nontemporal_store<T>(ptr: *mut T, val: T) {}
            pub fn ptr_offset_from<T>(ptr: *const T, base: *const T) -> isize {
                result!()
            }
            pub fn miri_start_panic<T>(data: T) {}
        }
    }

    pub mod isize {
        #[cfg(any(
            target_arch = "x86",
            target_arch = "mips",
            target_arch = "mips",
            target_arch = "powerpc",
            target_arch = "arm"
        ))]
        pub const MAX: isize = 2147483647;
        #[cfg(any(
            target_arch = "x86_64",
            target_arch = "powerpc64",
            target_arch = "aarch64"
        ))]
        pub const MAX: isize = 9223372036854775807;
        #[cfg(any(
            target_arch = "x86",
            target_arch = "mips",
            target_arch = "mips",
            target_arch = "powerpc",
            target_arch = "arm"
        ))]
        pub const MIN: isize = -2147483648;
        #[cfg(any(
            target_arch = "x86_64",
            target_arch = "powerpc64",
            target_arch = "aarch64"
        ))]
        pub const MIN: isize = -9223372036854775808;
    }

    pub mod iter {
        pub mod raw_vec {
            pub fn capacity_overflow() {}
        }

        pub mod result {
            pub fn unwrap_failed(_msg: &str, _error: &dyn std::fmt::Debug) {
                // todo: put something here that compiles OK here, but causes a diagnostic in the caller
                // i.e. something like a false precondition
            }
        }

        pub mod r#try {
            pub mod Try {
                pub fn from_error<T>() -> T {
                    result!()
                }

                pub fn into_result<T>() -> T {
                    result!()
                }
            }
        }

        pub mod traits {
            pub mod collect {
                pub trait FromIterator {
                    fn from_iter<T>() -> T {
                        result!()
                    }
                }
            }
        }
    }

    pub mod i8 {
        pub const MAX: i8 = 127;
        pub const MIN: i8 = -128;
    }

    pub mod i16 {
        pub const MAX: i16 = 32767;
        pub const MIN: i16 = -32768;
    }

    pub mod i32 {
        pub const MAX: i32 = 2147483647;
        pub const MIN: i32 = -2147483648;
    }

    pub mod i64 {
        pub const MAX: i64 = 9223372036854775807;
        pub const MIN: i64 = -9223372036854775808;
    }

    pub mod i128 {
        pub const MAX: i128 = 170141183460469231731687303715884105727;
        pub const MIN: i128 = -170141183460469231731687303715884105728;
    }

    pub mod mem {
        pub fn size_of__i8() -> usize {
            1
        }
        pub fn size_of__i16() -> usize {
            2
        }
        pub fn size_of__i32() -> usize {
            4
        }
        pub fn size_of__i64() -> usize {
            8
        }
        pub fn size_of__i128() -> usize {
            16
        }
        pub fn size_of__isize() -> usize {
            if cfg!(any(
                target_arch = "x86",
                tagret_arch = "mips",
                tagret_arch = "powerpc",
                tagret_arch = "arm"
            )) {
                4
            } else if cfg!(any(
                target_arch = "x86_64",
                tagret_arch = "powerpc64",
                tagret_arch = "aarch64"
            )) {
                8
            } else {
                panic!("Unsupported architecture");
            }
        }
        pub fn size_of__u8() -> usize {
            1
        }
        pub fn size_of__u16() -> usize {
            2
        }
        pub fn size_of__u32() -> usize {
            4
        }
        pub fn size_of__u64() -> usize {
            8
        }
        pub fn size_of__u128() -> usize {
            16
        }
        pub fn size_of__usize() -> usize {
            if cfg!(any(
                target_arch = "x86",
                tagret_arch = "mips",
                tagret_arch = "powerpc",
                tagret_arch = "arm"
            )) {
                4
            } else if cfg!(any(
                target_arch = "x86_64",
                tagret_arch = "powerpc64",
                tagret_arch = "aarch64"
            )) {
                8
            } else {
                panic!("Unsupported architecture");
            }
        }
    }

    pub mod num {
        pub mod implement_isize {
            pub fn max_value() -> isize {
                if cfg!(any(
                    target_arch = "x86",
                    tagret_arch = "mips",
                    tagret_arch = "powerpc",
                    tagret_arch = "arm"
                )) {
                    2147483647
                } else if cfg!(any(
                    target_arch = "x86_64",
                    tagret_arch = "powerpc64",
                    tagret_arch = "aarch64"
                )) {
                    9223372036854775807
                } else {
                    panic!("Unsupported architecture");
                }
            }
            pub fn min_value() -> isize {
                if cfg!(any(
                    target_arch = "x86",
                    tagret_arch = "mips",
                    tagret_arch = "powerpc",
                    tagret_arch = "arm"
                )) {
                    -2147483648
                } else if cfg!(any(
                    target_arch = "x86_64",
                    tagret_arch = "powerpc64",
                    tagret_arch = "aarch64"
                )) {
                    -9223372036854775808
                } else {
                    panic!("Unsupported architecture");
                }
            }
        }

        pub mod implement_i8 {
            pub fn max_value() -> i8 {
                127
            }
            pub fn min_value() -> i8 {
                -128
            }
        }

        pub mod implement_i16 {
            pub fn max_value() -> i16 {
                32767
            }
            pub fn min_value() -> i16 {
                -32768
            }
        }

        pub mod implement_i32 {
            pub fn max_value() -> i32 {
                2147483647
            }
            pub fn min_value() -> i32 {
                -2147483648
            }
        }

        pub mod implement_i64 {
            pub fn max_value() -> i64 {
                9223372036854775807
            }
            pub fn min_value() -> i64 {
                -9223372036854775808
            }
        }

        pub mod implement_i128 {
            pub fn max_value() -> i128 {
                170141183460469231731687303715884105727
            }
            pub fn min_value() -> i128 {
                -170141183460469231731687303715884105728
            }
        }

        pub mod implement_usize {
            pub fn max_value() -> usize {
                if cfg!(any(
                    target_arch = "x86",
                    tagret_arch = "mips",
                    tagret_arch = "powerpc",
                    tagret_arch = "arm"
                )) {
                    4294967295
                } else if cfg!(any(
                    target_arch = "x86_64",
                    tagret_arch = "powerpc64",
                    tagret_arch = "aarch64"
                )) {
                    18446744073709551615
                } else {
                    panic!("Unsupported architecture");
                }
            }
            pub fn min_value() -> usize {
                0
            }
            pub fn checked_add(_self: usize, value: usize) -> Option<usize> {
                if _self > max_value() - value {
                    None
                } else {
                    Some(_self + value)
                }
            }

            pub fn is_power_of_two(n: usize) -> bool {
                if cfg!(any(
                    target_arch = "x86",
                    tagret_arch = "mips",
                    tagret_arch = "powerpc",
                    tagret_arch = "arm"
                )) {
                    (n as u32).is_power_of_two()
                } else if cfg!(any(
                    target_arch = "x86_64",
                    tagret_arch = "powerpc64",
                    tagret_arch = "aarch64"
                )) {
                    (n as u64).is_power_of_two()
                } else {
                    panic!("Unsupported architecture");
                }
            }
        }

        pub mod implement_u8 {
            pub fn max_value() -> u8 {
                255
            }
            pub fn min_value() -> u8 {
                0
            }
            pub fn checked_add(_self: u8, value: u8) -> Option<u8> {
                if _self > max_value() - value {
                    None
                } else {
                    Some(_self + value)
                }
            }
            pub fn is_power_of_two(n: u8) -> bool {
                n == 1 << 0
                    || n == 1 << 1
                    || n == 1 << 2
                    || n == 1 << 3
                    || n == 1 << 4
                    || n == 1 << 5
                    || n == 1 << 6
                    || n == 1 << 7
            }
        }

        pub mod implement_u16 {
            pub fn max_value() -> u16 {
                65535
            }
            pub fn min_value() -> u16 {
                0
            }

            pub fn is_power_of_two(n: u16) -> bool {
                n == 1 << 0
                    || n == 1 << 1
                    || n == 1 << 2
                    || n == 1 << 3
                    || n == 1 << 4
                    || n == 1 << 5
                    || n == 1 << 6
                    || n == 1 << 7
                    || n == 1 << 8
                    || n == 1 << 9
                    || n == 1 << 10
                    || n == 1 << 11
                    || n == 1 << 12
                    || n == 1 << 13
                    || n == 1 << 14
                    || n == 1 << 15
            }
        }

        pub mod implement_u32 {
            pub fn max_value() -> u32 {
                4294967295
            }
            pub fn min_value() -> u32 {
                0
            }
        }

        pub mod implement_u64 {
            pub fn max_value() -> u64 {
                18446744073709551615
            }
            pub fn min_value() -> u64 {
                0
            }
        }

        pub mod implement_u128 {
            pub fn max_value() -> u128 {
                340282366920938463463374607431768211455
            }
            pub fn min_value() -> u128 {
                0
            }
        }
    }

    pub mod ops {
        pub mod arith {
            pub mod Add {
                pub fn add__usize_usize(x: usize, y: usize) -> usize {
                    x + y
                }
            }
        }
    }

    pub mod option {
        pub fn expect_failed() {
            panic!("expect failed");
        }
    }

    pub mod ptr {
        pub fn drop_in_place() {}
    }

    pub mod result {
        fn unwrap_failed(msg: &str) -> ! {
            panic!("{}", msg)
        }
    }

    pub mod slice {

        pub mod SliceIndex {
            pub fn get<T>() -> T {
                result!()
            }

            pub fn get_unchecked<T>() -> T {
                result!()
            }
        }
    }

    pub mod str {
        pub mod implement_str {
            pub fn is_empty(_self: &str) -> bool {
                _self.len() == 0
            }
        }
    }

    pub mod usize {
        #[cfg(any(
            target_arch = "x86",
            target_arch = "mips",
            target_arch = "mips",
            target_arch = "powerpc",
            target_arch = "arm"
        ))]
        pub const MAX: usize = 4294967295;
        #[cfg(any(
            target_arch = "x86_64",
            target_arch = "powerpc64",
            target_arch = "aarch64"
        ))]
        pub const MAX: usize = 18446744073709551615;
        pub const MIN: usize = 0;
    }

    pub mod u8 {
        pub const MAX: u8 = 255;
        pub const MIN: u8 = 0;
    }

    pub mod u16 {
        pub const MAX: u16 = 65535;
        pub const MIN: u16 = 0;
    }

    pub mod u32 {
        pub const MAX: u32 = 4294967295;
        pub const MIN: u32 = 0;
    }

    pub mod u64 {
        pub const MAX: u64 = 18446744073709551615;
        pub const MIN: u64 = 0;
    }

    pub mod u128 {
        pub const MAX: u128 = 340282366920938463463374607431768211455;
        pub const MIN: u128 = 0;
    }
}

pub mod libc {
    pub mod unix {
        pub mod _1 {
            pub fn pthread_mutex_lock() -> u64 {
                0
            }

            pub fn pthread_cond_signal() -> u64 {
                0
            }

            pub fn pthread_mutex_unlock() -> u64 {
                0
            }
        }
    }
}

pub mod log {
    pub fn __private_api_log() {}
}

pub mod rand {
    pub mod rngs {
        pub mod std {
            pub struct StdRng {
                _value: usize,
            }

            impl StdRng {
                pub fn new() -> StdRng {
                    StdRng { _value: 0 }
                }
            }
        }
    }

    pub mod Rng {
        use crate::foreign_contracts::rand::rngs;
        pub fn gen_range__rand_rngs_std_StdRng_usize_usize_usize(
            _self: &rngs::std::StdRng,
            lower: usize,
            upper: usize,
        ) -> usize {
            let res = result!();
            assume!(res >= lower && res < upper);
            res
        }
        pub fn gen_range__rand_rngs_std_StdRng_u8_u8_u8(
            _self: &rngs::std::StdRng,
            lower: u8,
            upper: u8,
        ) -> u8 {
            let res = result!();
            assume!(res >= lower && res < upper);
            res
        }
        pub fn gen_range__rand_rngs_std_StdRng_u16_u16_u16(
            _self: &rngs::std::StdRng,
            lower: u16,
            upper: u16,
        ) -> u16 {
            let res = result!();
            assume!(res >= lower && res < upper);
            res
        }
        pub fn gen_range__rand_rngs_std_StdRng_u32_u32_u32(
            _self: &rngs::std::StdRng,
            lower: u32,
            upper: u32,
        ) -> u32 {
            let res = result!();
            assume!(res >= lower && res < upper);
            res
        }
        pub fn gen_range__rand_rngs_std_StdRng_u64_u64_u64(
            _self: &rngs::std::StdRng,
            lower: u64,
            upper: u64,
        ) -> u64 {
            let res = result!();
            assume!(res >= lower && res < upper);
            res
        }
        pub fn gen_range__rand_rngs_std_StdRng_f32_f32_f32(
            _self: &rngs::std::StdRng,
            lower: f32,
            upper: f32,
        ) -> f32 {
            let res = result!();
            assume!(res >= lower && res < upper);
            res
        }
        pub fn gen_range__rand_rngs_std_StdRng_f64_f64_f64(
            _self: &rngs::std::StdRng,
            lower: f64,
            upper: f64,
        ) -> f64 {
            let res = result!();
            assume!(res >= lower && res < upper);
            res
        }
        pub fn gen_bool__rand_rngs_std_StdRng(_self: &rngs::std::StdRng, probability: f64) -> bool {
            precondition!(probability >= 0.0 && probability <= 1.0);
            result!()
        }
    }
}

pub mod std {
    pub mod collections {
        pub mod hash {
            pub mod map {
                pub mod implement_map {
                    pub fn new<T>() -> T {
                        result!()
                    }
                }
            }
        }
    }

    pub mod fmt {
        pub struct Arguments<'a> {
            // Format string pieces to print.
            pub pieces: &'a [&'a str],
        }

        impl<'a> Arguments<'a> {
            pub fn new_v1(pieces: &'a [&'a str]) -> Arguments<'a> {
                Arguments { pieces }
            }
        }
    }

    pub mod io {
        pub mod stdio {
            use crate::foreign_contracts::core::fmt;
            pub fn _print(_args: fmt::Arguments<'_>) {}
        }
    }

    pub mod result {}

    pub mod sys {
        pub mod unix {
            pub mod fast_thread_local {
                pub fn register_dtor() {}
            }
        }
    }

    pub mod thread {
        pub fn yield_now() {}
    }

    pub mod time {
        pub mod implement {
            pub fn now<T>() -> T {
                result!()
            }
        }
    }
}
