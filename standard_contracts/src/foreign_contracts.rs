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
        pub fn handle_alloc_error() {
            // Not something that can be reasonably detected with static analysis, so ignore.
            assume_unreachable!();
        }
    }

    pub mod fmt {
        pub fn format() -> String {
            result!()
        }
    }

    pub mod raw_vec {
        pub fn capacity_overflow() {
            assume_unreachable!("capacity overflow");
        }
    }

    pub mod slice {
        pub fn merge_sort<T, F>(v: &mut [T], mut is_less: F)
        where
            F: FnMut(&T, &T) -> bool,
        {
            //todo: havoc v
            //todo: provide a post condition once quantifiers are supported
        }
    }

    pub mod vec {
        pub mod implement {
            pub mod insert {
                fn assert_failed(index: usize, len: usize) -> ! {
                    panic!(
                        "insertion index (is {}) should be <= len (is {})",
                        index, len
                    );
                }
            }

            pub mod remove {
                fn assert_failed(index: usize, len: usize) -> ! {
                    panic!("removal index (is {}) should be < len (is {})", index, len);
                }
            }

            pub mod split_off {
                fn assert_failed(at: usize, len: usize) -> ! {
                    panic!("`at` split index (is {}) should be <= len (is {})", at, len);
                }
            }

            pub mod swap_remove {
                fn assert_failed(index: usize, len: usize) {
                    panic!(
                        "swap_remove index (is {}) should be < len (is {})",
                        index, len
                    );
                }
            }
        }
        pub mod SpecExtend {
            pub fn spec_extend() {}
        }
    }
}

pub mod core {
    pub mod alloc {
        pub mod AllocRef {
            pub fn alloc<T>(
                _self: T,
                layout: std::alloc::Layout,
            ) -> Result<(std::ptr::NonNull<u8>, usize), core::alloc::AllocError>
            where
                T: std::alloc::AllocRef,
            {
                unsafe {
                    let buf = std::alloc::alloc(layout);
                    Ok((std::ptr::NonNull::<u8>::new_unchecked(buf), layout.size()))
                }
            }

            pub fn alloc_zeroed<T>(
                _self: T,
                layout: std::alloc::Layout,
            ) -> Result<(std::ptr::NonNull<u8>, usize), core::alloc::AllocError>
            where
                T: std::alloc::AllocRef,
            {
                unsafe {
                    let buf = std::alloc::alloc_zeroed(layout);
                    Ok((std::ptr::NonNull::<u8>::new_unchecked(buf), layout.size()))
                }
            }

            pub fn dealloc<T>(_self: T, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout)
            where
                T: std::alloc::AllocRef,
            {
                unsafe {
                    std::alloc::dealloc(ptr.as_ptr(), layout);
                }
            }

            pub fn realloc<T>(
                _self: T,
                ptr: std::ptr::NonNull<u8>,
                layout: std::alloc::Layout,
                new_size: usize,
            ) -> Result<(std::ptr::NonNull<u8>, usize), core::alloc::AllocError>
            where
                T: std::alloc::AllocRef,
            {
                unsafe {
                    let buf = std::alloc::realloc(ptr.as_ptr(), layout, new_size);
                    Ok((std::ptr::NonNull::<u8>::new_unchecked(buf), layout.size()))
                }
            }
        }

        pub mod raw_vec {
            pub fn capacity_overflow() {
                assume_unreachable!("capacity overflow");
            }
        }
    }

    pub mod clone {
        pub mod Clone {
            pub fn clone__array_u8(_self: &u8) -> u8 {
                *_self
            }

            pub fn clone__array_u32(_self: &u32) -> u32 {
                *_self
            }

            pub fn clone__tuple_2_i32_i32(_self: &(i32, i32)) -> (i32, i32) {
                (_self.0, _self.1)
            }

            pub fn clone__tuple_2_libra_crypto_ed25519_Ed25519Signature_u8<T: Clone>(
                _self: &(T, u8),
            ) -> (T, u8) {
                // todo: do not call clone here
                (_self.0.clone(), _self.1)
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
            fn cmp__i8(a: &i8, b: &i8) -> std::cmp::Ordering {
                if *a < *b {
                    std::cmp::Ordering::Less
                } else if *a == *b {
                    std::cmp::Ordering::Equal
                } else {
                    std::cmp::Ordering::Greater
                }
            }
            fn cmp__i16(a: &i16, b: &i16) -> std::cmp::Ordering {
                if *a < *b {
                    std::cmp::Ordering::Less
                } else if *a == *b {
                    std::cmp::Ordering::Equal
                } else {
                    std::cmp::Ordering::Greater
                }
            }
            fn cmp__i32(a: &i32, b: &i32) -> std::cmp::Ordering {
                if *a < *b {
                    std::cmp::Ordering::Less
                } else if *a == *b {
                    std::cmp::Ordering::Equal
                } else {
                    std::cmp::Ordering::Greater
                }
            }
            fn cmp__i64(a: &i64, b: &i64) -> std::cmp::Ordering {
                if *a < *b {
                    std::cmp::Ordering::Less
                } else if *a == *b {
                    std::cmp::Ordering::Equal
                } else {
                    std::cmp::Ordering::Greater
                }
            }
            fn cmp__i128(a: &i128, b: &i128) -> std::cmp::Ordering {
                if *a < *b {
                    std::cmp::Ordering::Less
                } else if *a == *b {
                    std::cmp::Ordering::Equal
                } else {
                    std::cmp::Ordering::Greater
                }
            }
            fn cmp__isize(a: &isize, b: &isize) -> std::cmp::Ordering {
                if *a < *b {
                    std::cmp::Ordering::Less
                } else if *a == *b {
                    std::cmp::Ordering::Equal
                } else {
                    std::cmp::Ordering::Greater
                }
            }
            fn cmp__u8(a: &u8, b: &u8) -> std::cmp::Ordering {
                if *a < *b {
                    std::cmp::Ordering::Less
                } else if *a == *b {
                    std::cmp::Ordering::Equal
                } else {
                    std::cmp::Ordering::Greater
                }
            }
            fn cmp__u16(a: &u16, b: &u16) -> std::cmp::Ordering {
                if *a < *b {
                    std::cmp::Ordering::Less
                } else if *a == *b {
                    std::cmp::Ordering::Equal
                } else {
                    std::cmp::Ordering::Greater
                }
            }
            fn cmp__u32(a: &u32, b: &u32) -> std::cmp::Ordering {
                if *a < *b {
                    std::cmp::Ordering::Less
                } else if *a == *b {
                    std::cmp::Ordering::Equal
                } else {
                    std::cmp::Ordering::Greater
                }
            }
            fn cmp__u64(a: &u64, b: &u64) -> std::cmp::Ordering {
                if *a < *b {
                    std::cmp::Ordering::Less
                } else if *a == *b {
                    std::cmp::Ordering::Equal
                } else {
                    std::cmp::Ordering::Greater
                }
            }
            fn cmp__u128(a: &u128, b: &u128) -> std::cmp::Ordering {
                if *a < *b {
                    std::cmp::Ordering::Less
                } else if *a == *b {
                    std::cmp::Ordering::Equal
                } else {
                    std::cmp::Ordering::Greater
                }
            }
            fn cmp__usize(a: &usize, b: &usize) -> std::cmp::Ordering {
                if *a < *b {
                    std::cmp::Ordering::Less
                } else if *a == *b {
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
        pub mod AsRef {
            pub fn as_ref__trait_aead_Buffer_slice_u8<T>(_self: &T) -> &T {
                _self
            }
        }

        pub mod Into {
            pub fn into__usize_usize(t: usize) -> usize {
                t
            }
        }

        pub mod implement_convert {
            pub fn try_into__ref_slice_u8_array_u8(arg: &[u8]) -> &[u8] {
                arg
            }
        }
    }

    pub mod core_arch {
        pub mod simd_llvm {
            //pub fn simd_select_bitmask
            pub fn simd_eq<T, U>(x: T, y: T) -> U {
                result!()
            }
            pub fn simd_ne<T, U>(x: T, y: T) -> U {
                result!()
            }
            pub fn simd_lt<T, U>(x: T, y: T) -> U {
                result!()
            }
            pub fn simd_le<T, U>(x: T, y: T) -> U {
                result!()
            }
            pub fn simd_gt<T, U>(x: T, y: T) -> U {
                result!()
            }
            pub fn simd_ge<T, U>(x: T, y: T) -> U {
                result!()
            }

            pub fn simd_shuffle2<T, U>(x: T, y: T, idx: [u32; 2]) -> U {
                result!()
            }
            fn simd_shuffle4<T, U>(x: T, y: T, idx: [u32; 4]) -> U {
                result!()
            }
            fn simd_shuffle8<T, U>(x: T, y: T, idx: [u32; 8]) -> U {
                result!()
            }
            fn simd_shuffle16<T, U>(x: T, y: T, idx: [u32; 16]) -> U {
                result!()
            }
            fn simd_shuffle32<T, U>(x: T, y: T, idx: [u32; 32]) -> U {
                result!()
            }
            fn simd_shuffle64<T, U>(x: T, y: T, idx: [u32; 64]) -> U {
                result!()
            }
            fn simd_shuffle128<T, U>(x: T, y: T, idx: [u32; 128]) -> U {
                result!()
            }

            fn simd_insert<T, U>(x: T, idx: u32, val: U) -> T {
                result!()
            }
            fn simd_extract<T, U>(x: T, idx: u32) -> U {
                result!()
            }
            //pub fn simd_select
            fn simd_bitmask<T, U>(x: T) -> U {
                result!()
            }

            fn simd_cast<T, U>(x: T) -> U {
                result!()
            }

            fn simd_add<T>(x: T, y: T) -> T {
                result!()
            }
            fn simd_sub<T>(x: T, y: T) -> T {
                result!()
            }
            fn simd_mul<T>(x: T, y: T) -> T {
                result!()
            }
            fn simd_div<T>(x: T, y: T) -> T {
                result!()
            }
            fn simd_shl<T>(x: T, y: T) -> T {
                result!()
            }
            fn simd_shr<T>(x: T, y: T) -> T {
                result!()
            }
            fn simd_and<T>(x: T, y: T) -> T {
                result!()
            }
            fn simd_or<T>(x: T, y: T) -> T {
                result!()
            }
            fn simd_xor<T>(x: T, y: T) -> T {
                result!()
            }

            fn simd_saturating_add<T>(x: T, y: T) -> T {
                result!()
            }
            fn simd_saturating_sub<T>(x: T, y: T) -> T {
                result!()
            }

            fn simd_gather<T, U, V>(values: T, pointers: U, mask: V) -> T {
                result!()
            }
            fn simd_scatter<T, U, V>(values: T, pointers: U, mask: V) {
                result!()
            }

            fn simd_reduce_add_unordered<T, U>(x: T) -> U {
                result!()
            }
            fn simd_reduce_mul_unordered<T, U>(x: T) -> U {
                result!()
            }
            fn simd_reduce_add_ordered<T, U>(x: T, acc: U) -> U {
                result!()
            }
            fn simd_reduce_mul_ordered<T, U>(x: T, acc: U) -> U {
                result!()
            }
            fn simd_reduce_min<T, U>(x: T) -> U {
                result!()
            }
            fn simd_reduce_max<T, U>(x: T) -> U {
                result!()
            }
            fn simd_reduce_min_nanless<T, U>(x: T) -> U {
                result!()
            }
            fn simd_reduce_max_nanless<T, U>(x: T) -> U {
                result!()
            }
            fn simd_reduce_and<T, U>(x: T) -> U {
                result!()
            }
            fn simd_reduce_or<T, U>(x: T) -> U {
                result!()
            }
            fn simd_reduce_xor<T, U>(x: T) -> U {
                result!()
            }
            fn simd_reduce_all<T>(x: T) -> bool {
                result!()
            }
            fn simd_reduce_any<T>(x: T) -> bool {
                result!()
            }

            fn simd_select<M, T>(m: M, a: T, b: T) -> T {
                result!()
            }
            fn simd_select_bitmask<M, T>(m: M, a: T, b: T) -> T {
                result!()
            }

            fn simd_fmin<T>(a: T, b: T) -> T {
                result!()
            }
            fn simd_fmax<T>(a: T, b: T) -> T {
                result!()
            }

            fn simd_fsqrt<T>(a: T) -> T {
                result!()
            }
            fn simd_fsin<T>(a: T) -> T {
                result!()
            }
            fn simd_fcos<T>(a: T) -> T {
                result!()
            }
            fn simd_fabs<T>(a: T) -> T {
                result!()
            }
            fn simd_floor<T>(a: T) -> T {
                result!()
            }
            fn simd_ceil<T>(a: T) -> T {
                result!()
            }
            fn simd_fexp<T>(a: T) -> T {
                result!()
            }
            fn simd_fexp2<T>(a: T) -> T {
                result!()
            }
            fn simd_flog10<T>(a: T) -> T {
                result!()
            }
            fn simd_flog2<T>(a: T) -> T {
                result!()
            }
            fn simd_flog<T>(a: T) -> T {
                result!()
            }
            //pub fn simd_fpowi
            //pub fn simd_fpow
            fn simd_fma<T>(a: T, b: T, c: T) -> T {
                result!()
            }
        }

        pub mod x86 {
            pub mod sse2 {
                pub fn pause() {}
                pub fn pmovmskb() -> i32 {
                    result!()
                }
            }
        }
    }

    pub mod fmt {
        use std::marker::PhantomData;

        pub struct Arguments<'a> {
            phantom: PhantomData<&'a str>,
        }

        pub struct ArgumentV1<'a> {
            phantom: PhantomData<&'a str>,
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

        pub unsafe fn atomic_cxchg<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            if abstract_value!(true) {
                *dst = src;
                (old, true)
            } else {
                (abstract_value!(old), false)
            }
        }
        pub unsafe fn atomic_cxchg_acq<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            if abstract_value!(true) {
                *dst = src;
                (old, true)
            } else {
                (abstract_value!(old), false)
            }
        }
        pub unsafe fn atomic_cxchg_rel<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            if abstract_value!(true) {
                *dst = src;
                (old, true)
            } else {
                (abstract_value!(old), false)
            }
        }
        pub unsafe fn atomic_cxchg_acqrel<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            if abstract_value!(true) {
                *dst = src;
                (old, true)
            } else {
                (abstract_value!(old), false)
            }
        }
        pub unsafe fn atomic_cxchg_relaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            if abstract_value!(true) {
                *dst = src;
                (old, true)
            } else {
                (abstract_value!(old), false)
            }
        }
        pub unsafe fn atomic_cxchg_failrelaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            if abstract_value!(true) {
                *dst = src;
                (old, true)
            } else {
                (abstract_value!(old), false)
            }
        }
        pub unsafe fn atomic_cxchg_failacq<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            if abstract_value!(true) {
                *dst = src;
                (old, true)
            } else {
                (abstract_value!(old), false)
            }
        }
        pub unsafe fn atomic_cxchg_acq_failrelaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            if abstract_value!(true) {
                *dst = src;
                (old, true)
            } else {
                (abstract_value!(old), false)
            }
        }
        pub unsafe fn atomic_cxchg_acqrel_failrelaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            if abstract_value!(true) {
                *dst = src;
                (old, true)
            } else {
                (abstract_value!(old), false)
            }
        }
        pub unsafe fn atomic_cxchgweak<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            if abstract_value!(true) {
                *dst = src;
                (old, true)
            } else {
                (abstract_value!(old), false)
            }
        }
        pub unsafe fn atomic_cxchgweak_acq<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            if abstract_value!(true) {
                *dst = src;
                (old, true)
            } else {
                (abstract_value!(old), false)
            }
        }
        pub unsafe fn atomic_cxchgweak_rel<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            if abstract_value!(true) {
                *dst = src;
                (old, true)
            } else {
                (abstract_value!(old), false)
            }
        }
        pub unsafe fn atomic_cxchgweak_acqrel<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            if abstract_value!(true) {
                *dst = src;
                (old, true)
            } else {
                (abstract_value!(old), false)
            }
        }
        pub unsafe fn atomic_cxchgweak_relaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            if abstract_value!(true) {
                *dst = src;
                (old, true)
            } else {
                (abstract_value!(old), false)
            }
        }
        pub unsafe fn atomic_cxchgweak_failrelaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            if abstract_value!(true) {
                *dst = src;
                (old, true)
            } else {
                (abstract_value!(old), false)
            }
        }
        pub unsafe fn atomic_cxchgweak_failacq<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            if abstract_value!(true) {
                *dst = src;
                (old, true)
            } else {
                (abstract_value!(old), false)
            }
        }
        pub unsafe fn atomic_cxchgweak_acq_failrelaxed<T>(
            dst: *mut T,
            old: T,
            src: T,
        ) -> (T, bool) {
            if abstract_value!(true) {
                *dst = src;
                (old, true)
            } else {
                (abstract_value!(old), false)
            }
        }
        pub unsafe fn atomic_cxchgweak_acqrel_failrelaxed<T>(
            dst: *mut T,
            old: T,
            src: T,
        ) -> (T, bool) {
            if abstract_value!(true) {
                *dst = src;
                (old, true)
            } else {
                (abstract_value!(old), false)
            }
        }
        pub unsafe fn atomic_load<T>(src: *const T) -> T
        where
            T: Copy,
        {
            *src
        }
        pub unsafe fn atomic_load_acq<T>(src: *const T) -> T
        where
            T: Copy,
        {
            *src
        }
        pub unsafe fn atomic_load_relaxed<T>(src: *const T) -> T
        where
            T: Copy,
        {
            *src
        }
        pub unsafe fn atomic_load_unordered<T>(src: *const T) -> T
        where
            T: Copy,
        {
            *src
        }
        pub unsafe fn atomic_store<T>(dst: *mut T, val: T)
        where
            T: Copy,
        {
            *dst = val;
        }
        pub unsafe fn atomic_store_rel<T>(dst: *mut T, val: T)
        where
            T: Copy,
        {
            *dst = val;
        }
        pub unsafe fn atomic_store_relaxed<T>(dst: *mut T, val: T)
        where
            T: Copy,
        {
            *dst = val;
        }
        pub unsafe fn atomic_store_unordered<T>(dst: *mut T, val: T)
        where
            T: Copy,
        {
            *dst = val;
        }
        pub unsafe fn atomic_xchg<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
        {
            let result = *dst;
            *dst = src;
            result
        }
        pub unsafe fn atomic_xchg_acq<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
        {
            let result = *dst;
            *dst = src;
            result
        }
        pub unsafe fn atomic_xchg_rel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
        {
            let result = *dst;
            *dst = src;
            result
        }
        pub unsafe fn atomic_xchg_acqrel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
        {
            let result = *dst;
            *dst = src;
            result
        }
        pub unsafe fn atomic_xchg_relaxed<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
        {
            let result = *dst;
            *dst = src;
            result
        }
        pub unsafe fn atomic_xadd<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::AddAssign,
        {
            let result = *dst;
            *dst += src;
            result
        }
        pub unsafe fn atomic_xadd_acq<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::AddAssign,
        {
            let result = *dst;
            *dst += src;
            result
        }
        pub unsafe fn atomic_xadd_rel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::AddAssign,
        {
            let result = *dst;
            *dst += src;
            result
        }
        pub unsafe fn atomic_xadd_acqrel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::AddAssign,
        {
            let result = *dst;
            *dst += src;
            result
        }
        pub unsafe fn atomic_xadd_relaxed<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::AddAssign,
        {
            let result = *dst;
            *dst += src;
            result
        }
        pub unsafe fn atomic_xsub<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::SubAssign,
        {
            let result = *dst;
            *dst -= src;
            result
        }
        pub unsafe fn atomic_xsub_acq<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::SubAssign,
        {
            let result = *dst;
            *dst -= src;
            result
        }
        pub unsafe fn atomic_xsub_rel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::SubAssign,
        {
            let result = *dst;
            *dst -= src;
            result
        }
        pub unsafe fn atomic_xsub_acqrel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::SubAssign,
        {
            let result = *dst;
            *dst -= src;
            result
        }
        pub unsafe fn atomic_xsub_relaxed<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::SubAssign,
        {
            let result = *dst;
            *dst -= src;
            result
        }
        pub unsafe fn atomic_and<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::BitAndAssign,
        {
            let result = *dst;
            *dst &= src;
            result
        }
        pub unsafe fn atomic_and_acq<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::BitAndAssign,
        {
            let result = *dst;
            *dst &= src;
            result
        }
        pub unsafe fn atomic_and_rel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::BitAndAssign,
        {
            let result = *dst;
            *dst &= src;
            result
        }
        pub unsafe fn atomic_and_acqrel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::BitAndAssign,
        {
            let result = *dst;
            *dst &= src;
            result
        }
        pub unsafe fn atomic_and_relaxed<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::BitAndAssign,
        {
            let result = *dst;
            *dst &= src;
            result
        }
        pub unsafe fn atomic_nand<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
        {
            let result = *dst;
            *dst = abstract_value!(result);
            result
        }
        pub unsafe fn atomic_nand_acq<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
        {
            let result = *dst;
            *dst = abstract_value!(result);
            result
        }
        pub unsafe fn atomic_nand_rel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
        {
            let result = *dst;
            *dst = abstract_value!(result);
            result
        }
        pub unsafe fn atomic_nand_acqrel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
        {
            let result = *dst;
            *dst = abstract_value!(result);
            result
        }
        pub unsafe fn atomic_nand_relaxed<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
        {
            let result = *dst;
            *dst = abstract_value!(result);
            result
        }
        pub unsafe fn atomic_or<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::BitOrAssign,
        {
            let result = *dst;
            *dst |= src;
            result
        }
        pub unsafe fn atomic_or_acq<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::BitOrAssign,
        {
            let result = *dst;
            *dst |= src;
            result
        }
        pub unsafe fn atomic_or_rel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::BitOrAssign,
        {
            let result = *dst;
            *dst |= src;
            result
        }
        pub unsafe fn atomic_or_acqrel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::BitOrAssign,
        {
            let result = *dst;
            *dst |= src;
            result
        }
        pub unsafe fn atomic_or_relaxed<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::BitOrAssign,
        {
            let result = *dst;
            *dst |= src;
            result
        }
        pub unsafe fn atomic_xor<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::BitXorAssign,
        {
            let result = *dst;
            *dst ^= src;
            result
        }
        pub unsafe fn atomic_xor_acq<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::BitXorAssign,
        {
            let result = *dst;
            *dst ^= src;
            result
        }
        pub unsafe fn atomic_xor_rel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::BitXorAssign,
        {
            let result = *dst;
            *dst ^= src;
            result
        }
        pub unsafe fn atomic_xor_acqrel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::BitXorAssign,
        {
            let result = *dst;
            *dst ^= src;
            result
        }
        pub unsafe fn atomic_xor_relaxed<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: std::ops::BitXorAssign,
        {
            let result = *dst;
            *dst ^= src;
            result
        }
        pub unsafe fn atomic_max<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst <= src {
                src
            } else {
                *dst
            }
        }
        pub unsafe fn atomic_max_acq<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst <= src {
                src
            } else {
                *dst
            }
        }
        pub unsafe fn atomic_max_rel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst <= src {
                src
            } else {
                *dst
            }
        }
        pub unsafe fn atomic_max_acqrel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst <= src {
                src
            } else {
                *dst
            }
        }
        pub unsafe fn atomic_max_relaxed<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst <= src {
                src
            } else {
                *dst
            }
        }
        pub unsafe fn atomic_min<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst >= src {
                src
            } else {
                *dst
            }
        }
        pub unsafe fn atomic_min_acq<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst >= src {
                src
            } else {
                *dst
            }
        }
        pub unsafe fn atomic_min_rel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst >= src {
                src
            } else {
                *dst
            }
        }
        pub unsafe fn atomic_min_acqrel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst >= src {
                src
            } else {
                *dst
            }
        }
        pub unsafe fn atomic_min_relaxed<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst >= src {
                src
            } else {
                *dst
            }
        }
        pub unsafe fn atomic_umin<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst >= src {
                src
            } else {
                *dst
            }
        }
        pub unsafe fn atomic_umin_acq<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst >= src {
                src
            } else {
                *dst
            }
        }
        pub unsafe fn atomic_umin_rel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst >= src {
                src
            } else {
                *dst
            }
        }
        pub unsafe fn atomic_umin_acqrel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst >= src {
                src
            } else {
                *dst
            }
        }
        pub unsafe fn atomic_umin_relaxed<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst >= src {
                src
            } else {
                *dst
            }
        }
        pub unsafe fn atomic_umax<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst <= src {
                src
            } else {
                *dst
            }
        }
        pub unsafe fn atomic_umax_acq<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst <= src {
                src
            } else {
                *dst
            }
        }
        pub unsafe fn atomic_umax_rel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst <= src {
                src
            } else {
                *dst
            }
        }
        pub unsafe fn atomic_umax_acqrel<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst <= src {
                src
            } else {
                *dst
            }
        }
        pub unsafe fn atomic_umax_relaxed<T>(dst: *mut T, src: T) -> T
        where
            T: Copy,
            T: PartialOrd,
        {
            if *dst <= src {
                src
            } else {
                *dst
            }
        }
        pub fn prefetch_read_data<T>(data: *const T, locality: i32) {}
        pub fn prefetch_write_data<T>(data: *const T, locality: i32) {}
        pub fn prefetch_read_instruction<T>(data: *const T, locality: i32) {}
        pub fn prefetch_write_instruction<T>(data: *const T, locality: i32) {}

        pub mod _1 {
            pub fn assert_inhabited() {}
            pub fn assert_zero_valid() {}
            pub fn assert_uninit_valid() {}
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
            pub fn unreachable() {
                assume_unreachable!();
            }
            pub fn assume(b: bool) {
                assumed_postcondition!(b);
            }
            pub fn likely(b: bool) -> bool {
                b
            }
            pub fn unlikely(b: bool) -> bool {
                b
            }
            pub fn breakpoint() {}
            pub unsafe fn move_val_init<T>(dst: *mut T, src: T)
            where
                T: Copy,
            {
                *dst = src;
            }
            pub fn min_align_of<T>() -> usize {
                4
            }
            pub fn pref_align_of<T>() -> usize {
                result!()
            }
            pub fn type_name<T: ?Sized>() -> &'static str {
                result!()
            }
            pub fn type_id<T: ?Sized + 'static>() -> u64 {
                result!()
            }
            pub fn panic_if_uninhabited<T>() {
                // Compiler bootstrapping support. Nothing to do here when analyzing.
            }
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
            pub fn needs_drop<T>() -> bool {
                result!()
            }
            pub unsafe fn volatile_copy_nonoverlapping_memory<T>(
                dst: *mut T,
                src: *const T,
                count: usize,
            ) {
                std::intrinsics::copy_nonoverlapping(src, dst, count);
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

            pub fn fmaf32(a: f32, b: f32, c: f32) -> f32 {
                a * b + c
            }
            pub fn fmaf64(a: f64, b: f64, c: f64) -> f64 {
                a * b + c
            }

            add_with_overflow!(i8, i128, add_with_overflow__i8, std::i8::MAX);
            add_with_overflow!(i16, i128, add_with_overflow__i16, std::i16::MAX);
            add_with_overflow!(i32, i128, add_with_overflow__i32, std::i32::MAX);
            add_with_overflow!(i64, i128, add_with_overflow__i64, std::i64::MAX);
            add_with_overflow!(isize, i128, add_with_overflow__isize, std::isize::MAX);
            add_with_overflow!(u8, i128, add_with_overflow__u8, std::u8::MAX);
            add_with_overflow!(u16, i128, add_with_overflow__u16, std::u16::MAX);
            add_with_overflow!(u32, i128, add_with_overflow__u32, std::u32::MAX);
            add_with_overflow!(u64, i128, add_with_overflow__u64, std::u64::MAX);
            add_with_overflow!(usize, i128, add_with_overflow__usize, std::usize::MAX);

            sub_with_overflow!(i8, i128, sub_with_overflow__i8, std::i8::MAX);
            sub_with_overflow!(i16, i128, sub_with_overflow__i16, std::i16::MAX);
            sub_with_overflow!(i32, i128, sub_with_overflow__i32, std::i32::MAX);
            sub_with_overflow!(i64, i128, sub_with_overflow__i64, std::i64::MAX);
            sub_with_overflow!(isize, i128, sub_with_overflow__isize, std::isize::MAX);
            sub_with_overflow!(u8, i128, sub_with_overflow__u8, std::u8::MAX);
            sub_with_overflow!(u16, i128, sub_with_overflow__u16, std::u16::MAX);
            sub_with_overflow!(u32, i128, sub_with_overflow__u32, std::u32::MAX);
            sub_with_overflow!(u64, i128, sub_with_overflow__u64, std::u64::MAX);
            sub_with_overflow!(usize, i128, sub_with_overflow__usize, std::usize::MAX);

            // Performs an exact division, resulting in undefined behavior when
            // `x % y != 0` or `y == 0` or `x == T::min_value() && y == -1`
            exact_signed_div!(i8, exact_div__i8, std::i8::MIN);
            exact_signed_div!(i16, exact_div__i16, std::i16::MIN);
            exact_signed_div!(i32, exact_div__i32, std::i32::MIN);
            exact_signed_div!(i64, exact_div__i64, std::i64::MIN);
            exact_signed_div!(i128, exact_div__i128, std::i128::MIN);
            exact_signed_div!(isize, exact_div__isize, std::isize::MIN);
            exact_div!(u8, exact_div__u8);
            exact_div!(u16, exact_div__u16);
            exact_div!(u32, exact_div__u32);
            exact_div!(u64, exact_div__u64);
            exact_div!(u128, exact_div__u128);
            exact_div!(usize, exact_div__usize);

            unchecked_signed_div!(i8, unchecked_div__i8, std::i8::MIN);
            unchecked_signed_div!(i16, unchecked_div__i16, std::i16::MIN);
            unchecked_signed_div!(i32, unchecked_div__i32, std::i32::MIN);
            unchecked_signed_div!(i64, unchecked_div__i64, std::i64::MIN);
            unchecked_signed_div!(i128, unchecked_div__i128, std::i128::MIN);
            unchecked_signed_div!(isize, unchecked_div__isize, std::isize::MIN);
            unchecked_div!(u8, unchecked_div__u8);
            unchecked_div!(u16, unchecked_div__u16);
            unchecked_div!(u32, unchecked_div__u32);
            unchecked_div!(u64, unchecked_div__u64);
            unchecked_div!(u128, unchecked_div__u128);
            unchecked_div!(usize, unchecked_div__usize);

            unchecked_signed_rem!(i8, unchecked_rem__i8, std::i8::MIN);
            unchecked_signed_rem!(i16, unchecked_rem__i16, std::i16::MIN);
            unchecked_signed_rem!(i32, unchecked_rem__i32, std::i32::MIN);
            unchecked_signed_rem!(i64, unchecked_rem__i64, std::i64::MIN);
            unchecked_signed_rem!(i128, unchecked_rem__i128, std::i128::MIN);
            unchecked_signed_rem!(isize, unchecked_rem__isize, std::isize::MIN);
            unchecked_rem!(u8, unchecked_rem__u8);
            unchecked_rem!(u16, unchecked_rem__u16);
            unchecked_rem!(u32, unchecked_rem__u32);
            unchecked_rem!(u64, unchecked_rem__u64);
            unchecked_rem!(u128, unchecked_rem__u128);
            unchecked_rem!(usize, unchecked_rem__usize);

            unchecked_shl!(i8, unchecked_shl__i8);
            unchecked_shl!(i16, unchecked_shl__i16);
            unchecked_shl!(i32, unchecked_shl__i32);
            unchecked_shl!(i64, unchecked_shl__i64);
            unchecked_shl!(i128, unchecked_shl__i128);
            unchecked_shl!(isize, unchecked_shl__isize);
            unchecked_shl!(u8, unchecked_shl__u8);
            unchecked_shl!(u16, unchecked_shl__u16);
            unchecked_shl!(u32, unchecked_shl__u32);
            unchecked_shl!(u64, unchecked_shl__u64);
            unchecked_shl!(u128, unchecked_shl__u128);
            unchecked_shl!(usize, unchecked_shl__usize);

            unchecked_shr!(i8, unchecked_shr__i8);
            unchecked_shr!(i16, unchecked_shr__i16);
            unchecked_shr!(i32, unchecked_shr__i32);
            unchecked_shr!(i64, unchecked_shr__i64);
            unchecked_shr!(i128, unchecked_shr__i128);
            unchecked_shr!(isize, unchecked_shr__isize);
            unchecked_shr!(u8, unchecked_shr__u8);
            unchecked_shr!(u16, unchecked_shr__u16);
            unchecked_shr!(u32, unchecked_shr__u32);
            unchecked_shr!(u64, unchecked_shr__u64);
            unchecked_shr!(u128, unchecked_shr__u128);
            unchecked_shr!(usize, unchecked_shr__usize);

            unchecked_add!(i8, i128, unchecked_add__i8, std::i8::MAX);
            unchecked_add!(i16, i128, unchecked_add__i16, std::i16::MAX);
            unchecked_add!(i32, i128, unchecked_add__i32, std::i32::MAX);
            unchecked_add!(i64, i128, unchecked_add__i64, std::i64::MAX);
            unchecked_add!(i128, i128, unchecked_add__i128, std::i128::MAX);
            unchecked_add!(isize, i128, unchecked_add__isize, std::i128::MAX);
            unchecked_add!(u8, u128, unchecked_add__u8, std::u8::MAX);
            unchecked_add!(u16, u128, unchecked_add__u16, std::u16::MAX);
            unchecked_add!(u32, u128, unchecked_add__u32, std::u32::MAX);
            unchecked_add!(u64, u128, unchecked_add__u64, std::u64::MAX);
            unchecked_add!(u128, u128, unchecked_add__u128, std::u128::MAX);
            unchecked_add!(usize, u128, unchecked_add__usize, std::usize::MAX);

            unchecked_sub!(i8, unchecked_sub__i8, std::i8::MAX);
            unchecked_sub!(i16, unchecked_sub__i16, std::i16::MAX);
            unchecked_sub!(i32, unchecked_sub__i32, std::i32::MAX);
            unchecked_sub!(i64, unchecked_sub__i64, std::i64::MAX);
            unchecked_sub!(isize, unchecked_sub__isize, std::i128::MAX);
            unchecked_sub!(u8, unchecked_sub__u8, std::u8::MAX);
            unchecked_sub!(u16, unchecked_sub__u16, std::u16::MAX);
            unchecked_sub!(u32, unchecked_sub__u32, std::u32::MAX);
            unchecked_sub!(u64, unchecked_sub__u64, std::u64::MAX);
            pub fn unchecked_sub__usize(x: usize, y: usize) -> usize {
                // Do not enable these preconditions until the prover can handle ptr1 - ptr2
                // where ptr1 has been widened.
                // precondition!((x as i128) - (y as i128) >= 0);
                // precondition!((x as i128) - (y as i128) <= (std::usize::MAX as i128));
                x - y
            }

            unchecked_mul!(i8, i128, unchecked_mul__i8, std::i8::MAX);
            unchecked_mul!(i16, i128, unchecked_mul__i16, std::i16::MAX);
            unchecked_mul!(i32, i128, unchecked_mul__i32, std::i32::MAX);
            unchecked_mul!(i64, i128, unchecked_mul__i64, std::i64::MAX);
            unchecked_mul!(i128, i128, unchecked_mul__i128, std::i128::MAX);
            unchecked_mul!(isize, i128, unchecked_mul__isize, std::isize::MAX);
            unchecked_mul!(u8, u128, unchecked_mul__u8, std::u8::MAX);
            unchecked_mul!(u16, u128, unchecked_mul__u16, std::u16::MAX);
            unchecked_mul!(u32, u128, unchecked_mul__u32, std::u32::MAX);
            unchecked_mul!(u64, u128, unchecked_mul__u64, std::u64::MAX);
            unchecked_mul!(u128, u128, unchecked_mul__u128, std::u128::MAX);
            unchecked_mul!(usize, u128, unchecked_mul__usize, std::usize::MAX);

            // rotate_left: (X << (S % BW)) | (X >> ((BW - S) % BW))
            rotate_left!(i8, rotate_left__i8);
            rotate_left!(i16, rotate_left__i16);
            rotate_left!(i32, rotate_left__i32);
            rotate_left!(i64, rotate_left__i64);
            rotate_left!(i128, rotate_left__i128);
            rotate_left!(isize, rotate_left__isize);
            rotate_left!(u8, rotate_left__u8);
            rotate_left!(u16, rotate_left__u16);
            rotate_left!(u32, rotate_left__u32);
            rotate_left!(u64, rotate_left__u64);
            rotate_left!(u128, rotate_left__u128);
            rotate_left!(usize, rotate_left__usize);

            // rotate_right: (X << ((BW - S) % BW)) | (X >> (S % BW))
            rotate_right!(i8, rotate_right__i8);
            rotate_right!(i16, rotate_right__i16);
            rotate_right!(i32, rotate_right__i32);
            rotate_right!(i64, rotate_right__i64);
            rotate_right!(i128, rotate_right__i128);
            rotate_right!(isize, rotate_right__isize);
            rotate_right!(u8, rotate_right__u8);
            rotate_right!(u16, rotate_right__u16);
            rotate_right!(u32, rotate_right__u32);
            rotate_right!(u64, rotate_right__u64);
            rotate_right!(u128, rotate_right__u128);
            rotate_right!(usize, rotate_right__usize);

            // (a + b) mod 2<sup>N</sup>, where N is the width of T
            wrapping_add!(i8, i128, wrapping_add__i8, std::i8::MAX);
            wrapping_add!(i16, i128, wrapping_add__i16, std::i16::MAX);
            wrapping_add!(i32, i128, wrapping_add__i32, std::i32::MAX);
            wrapping_add!(i64, i128, wrapping_add__i64, std::i64::MAX);
            wrapping_add!(isize, i128, wrapping_add__isize, std::isize::MAX);
            wrapping_add!(u8, u128, wrapping_add__u8, std::u8::MAX);
            wrapping_add!(u16, u128, wrapping_add__u16, std::u16::MAX);
            wrapping_add!(u32, u128, wrapping_add__u32, std::u32::MAX);
            wrapping_add!(u64, u128, wrapping_add__u64, std::u64::MAX);
            wrapping_add!(usize, u128, wrapping_add__usize, std::usize::MAX);

            // (a - b) mod 2 ** N, where N is the width of T in bits.
            wrapping_sub!(i8, i128, wrapping_sub__i8, std::i8::MAX);
            wrapping_sub!(i16, i128, wrapping_sub__i16, std::i16::MAX);
            wrapping_sub!(i32, i128, wrapping_sub__i32, std::i32::MAX);
            wrapping_sub!(i64, i128, wrapping_sub__i64, std::i64::MAX);
            wrapping_sub!(isize, i128, wrapping_sub__isize, std::isize::MAX);
            wrapping_sub!(u8, i128, wrapping_sub__u8, std::u8::MAX);
            wrapping_sub!(u16, i128, wrapping_sub__u16, std::u16::MAX);
            wrapping_sub!(u32, i128, wrapping_sub__u32, std::u32::MAX);
            wrapping_sub!(u64, i128, wrapping_sub__u64, std::u64::MAX);
            wrapping_sub!(usize, i128, wrapping_sub__usize, std::usize::MAX);

            // (a * b) mod 2 ** N, where N is the width of T in bits.
            wrapping_mul!(i8, i128, wrapping_mul__i8, std::i8::MAX);
            wrapping_mul!(i16, i128, wrapping_mul__i16, std::i16::MAX);
            wrapping_mul!(i32, i128, wrapping_mul__i32, std::i32::MAX);
            wrapping_mul!(i64, i128, wrapping_mul__i64, std::i64::MAX);
            wrapping_mul!(isize, i128, wrapping_mul__isize, std::isize::MAX);
            wrapping_mul!(u8, u128, wrapping_mul__u8, std::u8::MAX);
            wrapping_mul!(u16, u128, wrapping_mul__u16, std::u16::MAX);
            wrapping_mul!(u32, u128, wrapping_mul__u32, std::u32::MAX);
            wrapping_mul!(u64, u128, wrapping_mul__u64, std::u64::MAX);
            wrapping_mul!(usize, u128, wrapping_mul__usize, std::usize::MAX);

            saturating_add!(i8, i128, saturating_add__i8, std::i8::MAX);
            saturating_add!(i16, i128, saturating_add__i16, std::i16::MAX);
            saturating_add!(i32, i128, saturating_add__i32, std::i32::MAX);
            saturating_add!(i64, i128, saturating_add__i64, std::i64::MAX);
            saturating_add!(isize, i128, saturating_add__isize, std::isize::MAX);
            saturating_add!(u8, u128, saturating_add__u8, std::u8::MAX);
            saturating_add!(u16, u128, saturating_add__u16, std::u16::MAX);
            saturating_add!(u32, u128, saturating_add__u32, std::u32::MAX);
            saturating_add!(u64, u128, saturating_add__u64, std::u64::MAX);
            saturating_add!(usize, u128, saturating_add__usize, std::usize::MAX);

            saturating_sub!(i8, saturating_sub__i8);
            saturating_sub!(i16, saturating_sub__i16);
            saturating_sub!(i32, saturating_sub__i32);
            saturating_sub!(i64, saturating_sub__i64);
            saturating_sub!(i128, saturating_sub__i128);
            saturating_sub!(isize, saturating_sub__isize);
            saturating_sub!(u8, saturating_sub__u8);
            saturating_sub!(u16, saturating_sub__u16);
            saturating_sub!(u32, saturating_sub__u32);
            saturating_sub!(u64, saturating_sub__u64);
            saturating_sub!(u128, saturating_sub__u128);
            saturating_sub!(usize, saturating_sub__usize);

            pub fn r#try(f: fn(*mut u8), data: *mut u8, local_ptr: *mut u8) -> i32 {
                result!()
            }
            pub fn nontemporal_store<T>(ptr: *mut T, val: T) {}
            pub fn ptr_offset_from<T>(ptr: *const T, base: *const T) -> isize {
                result!()
            }
            pub fn miri_start_panic<T>(data: T) {}
            pub fn count_code_region(_index: u32) {}
            pub fn ptr_guaranteed_eq<T>(ptr: *const T, other: *const T) -> bool {
                ptr == other
            }
            pub fn ptr_guaranteed_ne<T>(ptr: *const T, other: *const T) -> bool {
                ptr != other
            }
        }

        pub fn is_aligned_and_not_null<T>(ptr: *const T) -> bool {
            result!()
        }

        pub fn is_nonoverlapping<T>(src: *const T, dst: *const T, count: usize) -> bool {
            result!()
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
        pub mod adapters {
            pub mod zip {
                pub mod ZipImpl {
                    pub struct Zip<A, B> {
                        a: A,
                        b: B,
                        // index and len are only used by the specialized version of zip
                        index: usize,
                        len: usize,
                    }
                    pub fn new<A, B>(a: A, b: B) -> Zip<A, B> {
                        Zip {
                            a,
                            b,
                            index: 0,
                            len: 0,
                        }
                    }
                }
            }
        }

        pub mod raw_vec {
            pub fn capacity_overflow() {
                // Not something that can be prevented statically.
                // Never returns to its caller.
                assume_unreachable!("capacity overflow");
            }
        }

        pub mod result {
            pub fn unwrap_failed() {
                panic!("unwrap failed")
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
        pub mod implement_core_mem_Discriminant_generic_par_T {
            pub struct Discriminant(u128);

            fn eq<T>(_self: &Discriminant, rhs: &Discriminant) -> bool {
                (_self.0 as u128) == (rhs.0 as u128)
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

        pub mod index {
            pub mod Index {
                pub fn index__alloc_vec_Vec_u8_usize(_self: usize, slice: &[u8]) -> &u8 {
                    assume!(_self < slice.len());
                    &(*slice)[_self]
                }
            }

            pub mod IndexMut {
                pub fn index_mut__alloc_vec_Vec_u8_usize(
                    _self: usize,
                    slice: &mut [u8],
                ) -> &mut u8 {
                    assume!(_self < slice.len());
                    &mut (*slice)[_self]
                }
            }
        }
    }

    pub mod option {
        pub fn expect_failed() {
            // We currently treat expect as an explicit assumption made by the programmer for
            // reasons that are beyond the analyzer.
            assume_unreachable!();
        }
    }

    pub mod ptr {
        pub fn drop_in_place() {}

        pub unsafe fn swap<T>(x: *mut T, y: *mut T)
        where
            T: Copy,
        {
            let t = *x;
            *x = *y;
            *y = t;
        }

        pub unsafe fn swap_nonoverlapping_one<T>(x: *mut T, y: *mut T) {
            core::ptr::swap_nonoverlapping(x, y, 1);
        }

        pub unsafe fn swap_nonoverlapping_bytes(x: *mut u8, y: *mut u8, len: usize) {
            core::ptr::swap_nonoverlapping(x, y, len);
        }

        pub unsafe fn read<T>(src: *const T) -> T
        where
            T: Copy,
        {
            *src
        }

        pub unsafe fn read_unaligned<T>(src: *const T) -> T
        where
            T: Copy,
        {
            *src
        }

        pub unsafe fn read_volatile<T>(src: *const T) -> T
        where
            T: Copy,
        {
            *src
        }

        pub unsafe fn write<T>(dst: *mut T, src: T)
        where
            T: Copy,
        {
            *dst = src;
        }

        pub unsafe fn write_unaligned<T>(dst: *mut T, src: T)
        where
            T: Copy,
        {
            *dst = src;
        }

        pub unsafe fn write_volatile<T>(dst: *mut T, src: T)
        where
            T: Copy,
        {
            *dst = src;
        }

        pub unsafe fn align_offset<T: Sized>(p: *const T, a: usize) -> usize {
            // todo: implement inside MIRAI
            0
        }
    }

    pub mod result {
        fn unwrap_failed() -> ! {
            panic!("unwrap failed")
        }
    }

    pub mod slice {
        pub unsafe fn from_raw_parts<'a, T>(data: *const T, len: usize) -> &'a [T] {
            let result = std::slice::from_raw_parts(data, len);
            assumed_postcondition!(result.len() == len);
            result
        }

        pub mod implement {
            pub mod copy_from_slice {
                fn len_mismatch_fail(dst_len: usize, src_len: usize) {
                    panic!(
                        "source slice length ({}) does not match destination slice length ({})",
                        src_len, dst_len,
                    );
                }
            }
        }

        pub mod cmp {
            pub fn memcmp(_s1: *const u8, _s2: *const u8, _n: usize) -> i32 {
                result!()
            }
        }

        pub mod index {
            fn slice_end_index_len_fail(index: usize, len: usize) {
                panic!(
                    "range end index {} out of range for slice of length {}",
                    index, len
                );
            }

            pub fn slice_index_len_fail(_index: usize, _len: usize) {
                panic!("index out of range for slice");
            }

            pub fn slice_index_order_fail(_index: usize, _end: usize) {
                panic!("slice index starts at after slice end");
            }

            pub fn slice_index_overflow_fail() {
                panic!("attempted to index slice up to maximum usize");
            }

            fn slice_start_index_len_fail(index: usize, len: usize) -> ! {
                panic!(
                    "range start index {} out of range for slice of length {}",
                    index, len
                );
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

pub mod hashbrown {
    pub mod raw {
        pub mod implement {
            pub fn alloc_err<T>() -> T {
                result!()
            }
            pub fn capacity_overflow<T>() -> T {
                result!()
            }
        }
    }
}

pub mod libc {
    pub mod bsd {
        pub mod apple {
            pub fn dlsym() -> u64 {
                0
            }
        }
    }

    pub mod unix {
        pub mod _1 {
            pub fn dlsym() -> u64 {
                0
            }

            pub fn open() -> u64 {
                0
            }

            pub fn pthread_mutex_lock() -> u64 {
                0
            }

            pub fn pthread_cond_signal() -> u64 {
                0
            }

            pub fn pthread_mutex_unlock() -> u64 {
                0
            }

            pub fn read() -> u64 {
                0
            }
        }

        pub mod bsd {
            pub mod apple {
                pub fn __error() -> &'static i32 {
                    &-1
                }
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

pub mod sha2 {
    pub mod sha256 {
        pub mod x86 {
            pub fn compress(state: &mut [u32; 8], _blocks: &[[u8; 64]]) {
                *state = abstract_value!(*state);
            }
        }
    }
}

pub mod std {
    pub mod backtrace {
        pub mod implement_std_backtrace_Backtrace {
            pub fn capture() -> (std::backtrace::BacktraceStatus) {
                (std::backtrace::BacktraceStatus::Unsupported)
            }
        }
    }

    pub mod collections {
        pub mod hash {
            pub mod map {
                pub mod implement_std_collections_hash_map_RandomState {
                    pub struct RandomState {
                        pub k0: u64,
                        pub k1: u64,
                    }

                    pub fn new() -> RandomState {
                        RandomState {
                            k0: abstract_value!(0),
                            k1: abstract_value!(1),
                        }
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
        pub mod error {
            pub mod implement_std_io_error_Error {
                pub struct Error {
                    repr: Repr,
                }

                enum Repr {
                    Os(i32),
                    Simple(std::io::ErrorKind),
                    Custom(Box<Custom>),
                }

                struct Custom {
                    kind: std::io::ErrorKind,
                    error: Box<dyn std::error::Error + Send + Sync>,
                }

                pub fn kind(_self: Error) -> std::io::ErrorKind {
                    match _self.repr {
                        Repr::Os(code) => result!(),
                        Repr::Custom(ref c) => c.kind,
                        Repr::Simple(kind) => kind,
                    }
                }
                fn _new(
                    kind: std::io::ErrorKind,
                    error: Box<dyn std::error::Error + Send + Sync>,
                ) -> Error {
                    Error {
                        repr: Repr::Custom(Box::new(Custom { kind, error })),
                    }
                }
            }
        }
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
