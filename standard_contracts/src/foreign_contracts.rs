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

    pub mod string {
        pub mod implement_alloc_string_String {
            pub fn clone<T: Copy>(_self: T) -> T {
                //todo: provide mirai helper that does a deep clone
                _self
            }
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

            pub fn clone__array_u64(_self: &u64) -> u64 {
                *_self
            }

            pub fn clone__tuple_0() -> () {
                ()
            }

            pub fn clone__tuple_2_i32_i32(_self: &(i32, i32)) -> (i32, i32) {
                (_self.0, _self.1)
            }

            pub fn clone__tuple_2_libra_crypto_ed25519_Ed25519Signature_u8<T: Copy>(
                _self: &(T, u8),
            ) -> (T, u8) {
                (_self.0, _self.1)
            }

            pub fn clone__tuple_2_alloc_rc_Rc_mirai_abstract_value_AbstractValue_alloc_rc_Rc_mirai_abstract_value_AbstractValue<
                T: Copy,
            >(
                _self: &(T, T),
            ) -> (T, T) {
                (_self.0, _self.1)
            }

            pub fn clone__tuple_2_alloc_rc_Rc_mirai_path_Path_alloc_rc_Rc_mirai_abstract_value_AbstractValue<
                T: Copy,
                U: Copy,
            >(
                _self: &(T, U),
            ) -> (T, U) {
                (_self.0, _self.1)
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
            pub mod avx {
                use core::arch::x86_64::__m128;
                use core::arch::x86_64::__m128d;
                use core::arch::x86_64::__m256;
                use core::arch::x86_64::__m256d;
                type i8x16 = [i8; 16];
                type i8x32 = [i8; 32];
                type i16x8 = [i16; 8];
                type i16x16 = [i16; 16];
                type i32x4 = [i32; 4];
                type i32x8 = [i32; 8];
                type i64x2 = [i64; 2];
                type i64x4 = [i64; 4];
                type u8x16 = [u8; 16];
                type u8x32 = [u8; 32];
                type u16x8 = [u16; 8];
                type u16x16 = [u16; 16];
                type u32x4 = [u32; 4];
                type u32x8 = [u32; 8];
                type u64x2 = [u64; 2];
                type u64x4 = [u64; 4];

                fn addsubpd256(a: __m256d, b: __m256d) -> __m256d {
                    result!()
                }
                fn addsubps256(a: __m256, b: __m256) -> __m256 {
                    result!()
                }
                fn roundpd256(a: __m256d, b: i32) -> __m256d {
                    result!()
                }
                fn roundps256(a: __m256, b: i32) -> __m256 {
                    result!()
                }
                fn sqrtps256(a: __m256) -> __m256 {
                    result!()
                }
                fn vblendvpd(a: __m256d, b: __m256d, c: __m256d) -> __m256d {
                    result!()
                }
                fn vblendvps(a: __m256, b: __m256, c: __m256) -> __m256 {
                    result!()
                }
                fn vdpps(a: __m256, b: __m256, imm8: i32) -> __m256 {
                    result!()
                }
                fn vhaddpd(a: __m256d, b: __m256d) -> __m256d {
                    result!()
                }
                fn vhaddps(a: __m256, b: __m256) -> __m256 {
                    result!()
                }
                fn vhsubpd(a: __m256d, b: __m256d) -> __m256d {
                    result!()
                }
                fn vhsubps(a: __m256, b: __m256) -> __m256 {
                    result!()
                }
                fn vcmppd(a: __m128d, b: __m128d, imm8: i8) -> __m128d {
                    result!()
                }
                fn vcmppd256(a: __m256d, b: __m256d, imm8: u8) -> __m256d {
                    result!()
                }
                fn vcmpps(a: __m128, b: __m128, imm8: i8) -> __m128 {
                    result!()
                }
                fn vcmpps256(a: __m256, b: __m256, imm8: u8) -> __m256 {
                    result!()
                }
                fn vcmpsd(a: __m128d, b: __m128d, imm8: i8) -> __m128d {
                    result!()
                }
                fn vcmpss(a: __m128, b: __m128, imm8: i8) -> __m128 {
                    result!()
                }
                fn vcvtdq2ps(a: i32x8) -> __m256 {
                    result!()
                }
                fn vcvtpd2ps(a: __m256d) -> __m128 {
                    result!()
                }
                fn vcvtps2dq(a: __m256) -> i32x8 {
                    result!()
                }
                fn vcvttpd2dq(a: __m256d) -> i32x4 {
                    result!()
                }
                fn vcvtpd2dq(a: __m256d) -> i32x4 {
                    result!()
                }
                fn vcvttps2dq(a: __m256) -> i32x8 {
                    result!()
                }
                fn vzeroall() {}
                fn vzeroupper() {}
                fn vpermilps256(a: __m256, b: i32x8) -> __m256 {
                    result!()
                }
                fn vpermilps(a: __m128, b: i32x4) -> __m128 {
                    result!()
                }
                fn vpermilpd256(a: __m256d, b: i64x4) -> __m256d {
                    result!()
                }
                fn vpermilpd(a: __m128d, b: i64x2) -> __m128d {
                    result!()
                }
                fn vperm2f128ps256(a: __m256, b: __m256, imm8: i8) -> __m256 {
                    result!()
                }
                fn vperm2f128pd256(a: __m256d, b: __m256d, imm8: i8) -> __m256d {
                    result!()
                }
                fn vperm2f128si256(a: i32x8, b: i32x8, imm8: i8) -> i32x8 {
                    result!()
                }
                fn vbroadcastf128ps256(a: &__m128) -> __m256 {
                    result!()
                }
                fn vbroadcastf128pd256(a: &__m128d) -> __m256d {
                    result!()
                }
                fn storeupd256(mem_addr: *mut f64, a: __m256d) {
                    result!()
                }
                fn storeups256(mem_addr: *mut f32, a: __m256) {
                    result!()
                }
                fn storeudq256(mem_addr: *mut i8, a: i8x32) {
                    result!()
                }
                fn maskloadpd256(mem_addr: *const i8, mask: i64x4) -> __m256d {
                    result!()
                }
                fn maskstorepd256(mem_addr: *mut i8, mask: i64x4, a: __m256d) {
                    result!()
                }
                fn maskloadpd(mem_addr: *const i8, mask: i64x2) -> __m128d {
                    result!()
                }
                fn maskstorepd(mem_addr: *mut i8, mask: i64x2, a: __m128d) {
                    result!()
                }
                fn maskloadps256(mem_addr: *const i8, mask: i32x8) -> __m256 {
                    result!()
                }
                fn maskstoreps256(mem_addr: *mut i8, mask: i32x8, a: __m256) {
                    result!()
                }
                fn maskloadps(mem_addr: *const i8, mask: i32x4) -> __m128 {
                    result!()
                }
                fn maskstoreps(mem_addr: *mut i8, mask: i32x4, a: __m128) {
                    result!()
                }
                fn vlddqu(mem_addr: *const i8) -> i8x32 {
                    result!()
                }
                fn vrcpps(a: __m256) -> __m256 {
                    result!()
                }
                fn vrsqrtps(a: __m256) -> __m256 {
                    result!()
                }
                fn ptestz256(a: i64x4, b: i64x4) -> i32 {
                    result!()
                }
                fn ptestc256(a: i64x4, b: i64x4) -> i32 {
                    result!()
                }
                fn ptestnzc256(a: i64x4, b: i64x4) -> i32 {
                    result!()
                }
                fn vtestzpd256(a: __m256d, b: __m256d) -> i32 {
                    result!()
                }
                fn vtestcpd256(a: __m256d, b: __m256d) -> i32 {
                    result!()
                }
                fn vtestnzcpd256(a: __m256d, b: __m256d) -> i32 {
                    result!()
                }
                fn vtestzpd(a: __m128d, b: __m128d) -> i32 {
                    result!()
                }
                fn vtestcpd(a: __m128d, b: __m128d) -> i32 {
                    result!()
                }
                fn vtestnzcpd(a: __m128d, b: __m128d) -> i32 {
                    result!()
                }
                fn vtestzps256(a: __m256, b: __m256) -> i32 {
                    result!()
                }
                fn vtestcps256(a: __m256, b: __m256) -> i32 {
                    result!()
                }
                fn vtestnzcps256(a: __m256, b: __m256) -> i32 {
                    result!()
                }
                fn vtestzps(a: __m128, b: __m128) -> i32 {
                    result!()
                }
                fn vtestcps(a: __m128, b: __m128) -> i32 {
                    result!()
                }
                fn vtestnzcps(a: __m128, b: __m128) -> i32 {
                    result!()
                }
                fn movmskpd256(a: __m256d) -> i32 {
                    result!()
                }
                fn movmskps256(a: __m256) -> i32 {
                    result!()
                }
            }
            pub mod avx2 {
                use core::arch::x86_64::__m128;
                use core::arch::x86_64::__m128d;
                use core::arch::x86_64::__m256;
                use core::arch::x86_64::__m256d;
                type i8x16 = [i8; 16];
                type i8x32 = [i8; 32];
                type i16x8 = [i16; 8];
                type i16x16 = [i16; 16];
                type i32x4 = [i32; 4];
                type i32x8 = [i32; 8];
                type i64x2 = [i64; 2];
                type i64x4 = [i64; 4];
                type u8x16 = [u8; 16];
                type u8x32 = [u8; 32];
                type u16x8 = [u16; 8];
                type u16x16 = [u16; 16];
                type u32x4 = [u32; 4];
                type u32x8 = [u32; 8];
                type u64x2 = [u64; 2];
                type u64x4 = [u64; 4];

                fn pabsb(a: i8x32) -> u8x32 {
                    result!()
                }
                fn pabsw(a: i16x16) -> u16x16 {
                    result!()
                }
                fn pabsd(a: i32x8) -> u32x8 {
                    result!()
                }
                fn pavgb(a: u8x32, b: u8x32) -> u8x32 {
                    result!()
                }
                fn pavgw(a: u16x16, b: u16x16) -> u16x16 {
                    result!()
                }
                fn pblendvb(a: i8x32, b: i8x32, mask: i8x32) -> i8x32 {
                    result!()
                }
                fn phaddw(a: i16x16, b: i16x16) -> i16x16 {
                    result!()
                }
                fn phaddd(a: i32x8, b: i32x8) -> i32x8 {
                    result!()
                }
                fn phaddsw(a: i16x16, b: i16x16) -> i16x16 {
                    result!()
                }
                fn phsubw(a: i16x16, b: i16x16) -> i16x16 {
                    result!()
                }
                fn phsubd(a: i32x8, b: i32x8) -> i32x8 {
                    result!()
                }
                fn phsubsw(a: i16x16, b: i16x16) -> i16x16 {
                    result!()
                }
                fn pmaddwd(a: i16x16, b: i16x16) -> i32x8 {
                    result!()
                }
                fn pmaddubsw(a: u8x32, b: u8x32) -> i16x16 {
                    result!()
                }
                fn maskloadd(mem_addr: *const i8, mask: i32x4) -> i32x4 {
                    result!()
                }
                fn maskloadd256(mem_addr: *const i8, mask: i32x8) -> i32x8 {
                    result!()
                }
                fn maskloadq(mem_addr: *const i8, mask: i64x2) -> i64x2 {
                    result!()
                }
                fn maskloadq256(mem_addr: *const i8, mask: i64x4) -> i64x4 {
                    result!()
                }
                fn maskstored(mem_addr: *mut i8, mask: i32x4, a: i32x4) {
                    result!()
                }
                fn maskstored256(mem_addr: *mut i8, mask: i32x8, a: i32x8) {
                    result!()
                }
                fn maskstoreq(mem_addr: *mut i8, mask: i64x2, a: i64x2) {
                    result!()
                }
                fn maskstoreq256(mem_addr: *mut i8, mask: i64x4, a: i64x4) {
                    result!()
                }
                fn pmaxsw(a: i16x16, b: i16x16) -> i16x16 {
                    result!()
                }
                fn pmaxsd(a: i32x8, b: i32x8) -> i32x8 {
                    result!()
                }
                fn pmaxsb(a: i8x32, b: i8x32) -> i8x32 {
                    result!()
                }
                fn pmaxuw(a: u16x16, b: u16x16) -> u16x16 {
                    result!()
                }
                fn pmaxud(a: u32x8, b: u32x8) -> u32x8 {
                    result!()
                }
                fn pmaxub(a: u8x32, b: u8x32) -> u8x32 {
                    result!()
                }
                fn pminsw(a: i16x16, b: i16x16) -> i16x16 {
                    result!()
                }
                fn pminsd(a: i32x8, b: i32x8) -> i32x8 {
                    result!()
                }
                fn pminsb(a: i8x32, b: i8x32) -> i8x32 {
                    result!()
                }
                fn pminuw(a: u16x16, b: u16x16) -> u16x16 {
                    result!()
                }
                fn pminud(a: u32x8, b: u32x8) -> u32x8 {
                    result!()
                }
                fn pminub(a: u8x32, b: u8x32) -> u8x32 {
                    result!()
                }
                fn pmovmskb(a: i8x32) -> i32 {
                    result!()
                }
                fn mpsadbw(a: u8x32, b: u8x32, imm8: i32) -> u16x16 {
                    result!()
                }
                fn pmulhuw(a: u16x16, b: u16x16) -> u16x16 {
                    result!()
                }
                fn pmulhw(a: i16x16, b: i16x16) -> i16x16 {
                    result!()
                }
                fn pmuldq(a: i32x8, b: i32x8) -> i64x4 {
                    result!()
                }
                fn pmuludq(a: u32x8, b: u32x8) -> u64x4 {
                    result!()
                }
                fn pmulhrsw(a: i16x16, b: i16x16) -> i16x16 {
                    result!()
                }
                fn packsswb(a: i16x16, b: i16x16) -> i8x32 {
                    result!()
                }
                fn packssdw(a: i32x8, b: i32x8) -> i16x16 {
                    result!()
                }
                fn packuswb(a: i16x16, b: i16x16) -> u8x32 {
                    result!()
                }
                fn packusdw(a: i32x8, b: i32x8) -> u16x16 {
                    result!()
                }
                fn psadbw(a: u8x32, b: u8x32) -> u64x4 {
                    result!()
                }
                fn psignb(a: i8x32, b: i8x32) -> i8x32 {
                    result!()
                }
                fn psignw(a: i16x16, b: i16x16) -> i16x16 {
                    result!()
                }
                fn psignd(a: i32x8, b: i32x8) -> i32x8 {
                    result!()
                }
                fn psllw(a: i16x16, count: i16x8) -> i16x16 {
                    result!()
                }
                fn pslld(a: i32x8, count: i32x4) -> i32x8 {
                    result!()
                }
                fn psllq(a: i64x4, count: i64x2) -> i64x4 {
                    result!()
                }
                fn pslliw(a: i16x16, imm8: i32) -> i16x16 {
                    result!()
                }
                fn psllid(a: i32x8, imm8: i32) -> i32x8 {
                    result!()
                }
                fn pslliq(a: i64x4, imm8: i32) -> i64x4 {
                    result!()
                }
                fn psllvd(a: i32x4, count: i32x4) -> i32x4 {
                    result!()
                }
                fn psllvd256(a: i32x8, count: i32x8) -> i32x8 {
                    result!()
                }
                fn psllvq(a: i64x2, count: i64x2) -> i64x2 {
                    result!()
                }
                fn psllvq256(a: i64x4, count: i64x4) -> i64x4 {
                    result!()
                }
                fn psraw(a: i16x16, count: i16x8) -> i16x16 {
                    result!()
                }
                fn psrad(a: i32x8, count: i32x4) -> i32x8 {
                    result!()
                }
                fn psraiw(a: i16x16, imm8: i32) -> i16x16 {
                    result!()
                }
                fn psraid(a: i32x8, imm8: i32) -> i32x8 {
                    result!()
                }
                fn psravd(a: i32x4, count: i32x4) -> i32x4 {
                    result!()
                }
                fn psravd256(a: i32x8, count: i32x8) -> i32x8 {
                    result!()
                }
                fn psrlw(a: i16x16, count: i16x8) -> i16x16 {
                    result!()
                }
                fn psrld(a: i32x8, count: i32x4) -> i32x8 {
                    result!()
                }
                fn psrlq(a: i64x4, count: i64x2) -> i64x4 {
                    result!()
                }
                fn psrliw(a: i16x16, imm8: i32) -> i16x16 {
                    result!()
                }
                fn psrlid(a: i32x8, imm8: i32) -> i32x8 {
                    result!()
                }
                fn psrliq(a: i64x4, imm8: i32) -> i64x4 {
                    result!()
                }
                fn psrlvd(a: i32x4, count: i32x4) -> i32x4 {
                    result!()
                }
                fn psrlvd256(a: i32x8, count: i32x8) -> i32x8 {
                    result!()
                }
                fn psrlvq(a: i64x2, count: i64x2) -> i64x2 {
                    result!()
                }
                fn psrlvq256(a: i64x4, count: i64x4) -> i64x4 {
                    result!()
                }
                fn pshufb(a: u8x32, b: u8x32) -> u8x32 {
                    result!()
                }
                fn permd(a: u32x8, b: u32x8) -> u32x8 {
                    result!()
                }
                fn permps(a: __m256, b: i32x8) -> __m256 {
                    result!()
                }
                fn vperm2i128(a: i64x4, b: i64x4, imm8: i8) -> i64x4 {
                    result!()
                }
                fn pgatherdd(
                    src: i32x4,
                    slice: *const i8,
                    offsets: i32x4,
                    mask: i32x4,
                    scale: i8,
                ) -> i32x4 {
                    result!()
                }
                fn vpgatherdd(
                    src: i32x8,
                    slice: *const i8,
                    offsets: i32x8,
                    mask: i32x8,
                    scale: i8,
                ) -> i32x8 {
                    result!()
                }
                fn pgatherdq(
                    src: i64x2,
                    slice: *const i8,
                    offsets: i32x4,
                    mask: i64x2,
                    scale: i8,
                ) -> i64x2 {
                    result!()
                }
                fn vpgatherdq(
                    src: i64x4,
                    slice: *const i8,
                    offsets: i32x4,
                    mask: i64x4,
                    scale: i8,
                ) -> i64x4 {
                    result!()
                }
                fn pgatherqd(
                    src: i32x4,
                    slice: *const i8,
                    offsets: i64x2,
                    mask: i32x4,
                    scale: i8,
                ) -> i32x4 {
                    result!()
                }
                fn vpgatherqd(
                    src: i32x4,
                    slice: *const i8,
                    offsets: i64x4,
                    mask: i32x4,
                    scale: i8,
                ) -> i32x4 {
                    result!()
                }
                fn pgatherqq(
                    src: i64x2,
                    slice: *const i8,
                    offsets: i64x2,
                    mask: i64x2,
                    scale: i8,
                ) -> i64x2 {
                    result!()
                }
                fn vpgatherqq(
                    src: i64x4,
                    slice: *const i8,
                    offsets: i64x4,
                    mask: i64x4,
                    scale: i8,
                ) -> i64x4 {
                    result!()
                }
                fn pgatherdpd(
                    src: __m128d,
                    slice: *const i8,
                    offsets: i32x4,
                    mask: __m128d,
                    scale: i8,
                ) -> __m128d {
                    result!()
                }
                fn vpgatherdpd(
                    src: __m256d,
                    slice: *const i8,
                    offsets: i32x4,
                    mask: __m256d,
                    scale: i8,
                ) -> __m256d {
                    result!()
                }
                fn pgatherqpd(
                    src: __m128d,
                    slice: *const i8,
                    offsets: i64x2,
                    mask: __m128d,
                    scale: i8,
                ) -> __m128d {
                    result!()
                }
                fn vpgatherqpd(
                    src: __m256d,
                    slice: *const i8,
                    offsets: i64x4,
                    mask: __m256d,
                    scale: i8,
                ) -> __m256d {
                    result!()
                }
                fn pgatherdps(
                    src: __m128,
                    slice: *const i8,
                    offsets: i32x4,
                    mask: __m128,
                    scale: i8,
                ) -> __m128 {
                    result!()
                }
                fn vpgatherdps(
                    src: __m256,
                    slice: *const i8,
                    offsets: i32x8,
                    mask: __m256,
                    scale: i8,
                ) -> __m256 {
                    result!()
                }
                fn pgatherqps(
                    src: __m128,
                    slice: *const i8,
                    offsets: i64x2,
                    mask: __m128,
                    scale: i8,
                ) -> __m128 {
                    result!()
                }
                fn vpgatherqps(
                    src: __m128,
                    slice: *const i8,
                    offsets: i64x4,
                    mask: __m128,
                    scale: i8,
                ) -> __m128 {
                    result!()
                }
                fn vpslldq(a: i64x4, b: i32) -> i64x4 {
                    result!()
                }
                fn vpsrldq(a: i64x4, b: i32) -> i64x4 {
                    result!()
                }
            }
            pub mod sse2 {
                use core::arch::x86_64::__m128;
                use core::arch::x86_64::__m128d;
                use core::arch::x86_64::__m128i;
                use core::arch::x86_64::__m256;
                use core::arch::x86_64::__m256d;
                type i8x16 = [i8; 16];
                type i8x32 = [i8; 32];
                type i16x8 = [i16; 8];
                type i16x16 = [i16; 16];
                type i32x4 = [i32; 4];
                type i32x8 = [i32; 8];
                type i64x2 = [i64; 2];
                type i64x4 = [i64; 4];
                type u8x16 = [u8; 16];
                type u8x32 = [u8; 32];
                type u16x8 = [u16; 8];
                type u16x16 = [u16; 16];
                type u32x4 = [u32; 4];
                type u32x8 = [u32; 8];
                type u64x2 = [u64; 2];
                type u64x4 = [u64; 4];

                fn pause() {}
                fn clflush(p: *const u8) {}
                fn lfence() {}
                fn mfence() {}
                fn pavgb(a: u8x16, b: u8x16) -> u8x16 {
                    result!()
                }
                fn pavgw(a: u16x8, b: u16x8) -> u16x8 {
                    result!()
                }
                fn pmaddwd(a: i16x8, b: i16x8) -> i32x4 {
                    result!()
                }
                fn pmaxsw(a: i16x8, b: i16x8) -> i16x8 {
                    result!()
                }
                fn pmaxub(a: u8x16, b: u8x16) -> u8x16 {
                    result!()
                }
                fn pminsw(a: i16x8, b: i16x8) -> i16x8 {
                    result!()
                }
                fn pminub(a: u8x16, b: u8x16) -> u8x16 {
                    result!()
                }
                fn pmulhw(a: i16x8, b: i16x8) -> i16x8 {
                    result!()
                }
                fn pmulhuw(a: u16x8, b: u16x8) -> u16x8 {
                    result!()
                }
                fn pmuludq(a: u32x4, b: u32x4) -> u64x2 {
                    result!()
                }
                fn psadbw(a: u8x16, b: u8x16) -> u64x2 {
                    result!()
                }
                fn pslliw(a: i16x8, imm8: i32) -> i16x8 {
                    result!()
                }
                fn psllw(a: i16x8, count: i16x8) -> i16x8 {
                    result!()
                }
                fn psllid(a: i32x4, imm8: i32) -> i32x4 {
                    result!()
                }
                fn pslld(a: i32x4, count: i32x4) -> i32x4 {
                    result!()
                }
                fn pslliq(a: i64x2, imm8: i32) -> i64x2 {
                    result!()
                }
                fn psllq(a: i64x2, count: i64x2) -> i64x2 {
                    result!()
                }
                fn psraiw(a: i16x8, imm8: i32) -> i16x8 {
                    result!()
                }
                fn psraw(a: i16x8, count: i16x8) -> i16x8 {
                    result!()
                }
                fn psraid(a: i32x4, imm8: i32) -> i32x4 {
                    result!()
                }
                fn psrad(a: i32x4, count: i32x4) -> i32x4 {
                    result!()
                }
                fn psrliw(a: i16x8, imm8: i32) -> i16x8 {
                    result!()
                }
                fn psrlw(a: i16x8, count: i16x8) -> i16x8 {
                    result!()
                }
                fn psrlid(a: i32x4, imm8: i32) -> i32x4 {
                    result!()
                }
                fn psrld(a: i32x4, count: i32x4) -> i32x4 {
                    result!()
                }
                fn psrliq(a: i64x2, imm8: i32) -> i64x2 {
                    result!()
                }
                fn psrlq(a: i64x2, count: i64x2) -> i64x2 {
                    result!()
                }
                fn cvtdq2ps(a: i32x4) -> __m128 {
                    result!()
                }
                fn cvtps2dq(a: __m128) -> i32x4 {
                    result!()
                }
                fn maskmovdqu(a: i8x16, mask: i8x16, mem_addr: *mut i8) {
                    result!()
                }
                fn packsswb(a: i16x8, b: i16x8) -> i8x16 {
                    result!()
                }
                fn packssdw(a: i32x4, b: i32x4) -> i16x8 {
                    result!()
                }
                fn packuswb(a: i16x8, b: i16x8) -> u8x16 {
                    result!()
                }
                fn pmovmskb(a: i8x16) -> i32 {
                    result!()
                }
                fn maxsd(a: __m128d, b: __m128d) -> __m128d {
                    result!()
                }
                fn maxpd(a: __m128d, b: __m128d) -> __m128d {
                    result!()
                }
                fn minsd(a: __m128d, b: __m128d) -> __m128d {
                    result!()
                }
                fn minpd(a: __m128d, b: __m128d) -> __m128d {
                    result!()
                }
                fn sqrtsd(a: __m128d) -> __m128d {
                    result!()
                }
                fn sqrtpd(a: __m128d) -> __m128d {
                    result!()
                }
                fn cmpsd(a: __m128d, b: __m128d, imm8: i8) -> __m128d {
                    result!()
                }
                fn cmppd(a: __m128d, b: __m128d, imm8: i8) -> __m128d {
                    result!()
                }
                fn comieqsd(a: __m128d, b: __m128d) -> i32 {
                    result!()
                }
                fn comiltsd(a: __m128d, b: __m128d) -> i32 {
                    result!()
                }
                fn comilesd(a: __m128d, b: __m128d) -> i32 {
                    result!()
                }
                fn comigtsd(a: __m128d, b: __m128d) -> i32 {
                    result!()
                }
                fn comigesd(a: __m128d, b: __m128d) -> i32 {
                    result!()
                }
                fn comineqsd(a: __m128d, b: __m128d) -> i32 {
                    result!()
                }
                fn ucomieqsd(a: __m128d, b: __m128d) -> i32 {
                    result!()
                }
                fn ucomiltsd(a: __m128d, b: __m128d) -> i32 {
                    result!()
                }
                fn ucomilesd(a: __m128d, b: __m128d) -> i32 {
                    result!()
                }
                fn ucomigtsd(a: __m128d, b: __m128d) -> i32 {
                    result!()
                }
                fn ucomigesd(a: __m128d, b: __m128d) -> i32 {
                    result!()
                }
                fn ucomineqsd(a: __m128d, b: __m128d) -> i32 {
                    result!()
                }
                fn movmskpd(a: __m128d) -> i32 {
                    result!()
                }
                fn cvtpd2ps(a: __m128d) -> __m128 {
                    result!()
                }
                fn cvtps2pd(a: __m128) -> __m128d {
                    result!()
                }
                fn cvtpd2dq(a: __m128d) -> i32x4 {
                    result!()
                }
                fn cvtsd2si(a: __m128d) -> i32 {
                    result!()
                }
                fn cvtsd2ss(a: __m128, b: __m128d) -> __m128 {
                    result!()
                }
                fn cvtss2sd(a: __m128d, b: __m128) -> __m128d {
                    result!()
                }
                fn cvttpd2dq(a: __m128d) -> i32x4 {
                    result!()
                }
                fn cvttsd2si(a: __m128d) -> i32 {
                    result!()
                }
                fn cvttps2dq(a: __m128) -> i32x4 {
                    result!()
                }
                fn storeudq(mem_addr: *mut i8, a: __m128i) {
                    result!()
                }
                fn storeupd(mem_addr: *mut i8, a: __m128d) {
                    result!()
                }
            }
            pub mod sse3 {
                use core::arch::x86_64::__m128;
                use core::arch::x86_64::__m128d;
                use core::arch::x86_64::__m128i;
                use core::arch::x86_64::__m256;
                use core::arch::x86_64::__m256d;
                type i8x16 = [i8; 16];
                type i8x32 = [i8; 32];
                type i16x8 = [i16; 8];
                type i16x16 = [i16; 16];
                type i32x4 = [i32; 4];
                type i32x8 = [i32; 8];
                type i64x2 = [i64; 2];
                type i64x4 = [i64; 4];
                type u8x16 = [u8; 16];
                type u8x32 = [u8; 32];
                type u16x8 = [u16; 8];
                type u16x16 = [u16; 16];
                type u32x4 = [u32; 4];
                type u32x8 = [u32; 8];
                type u64x2 = [u64; 2];
                type u64x4 = [u64; 4];

                fn addsubps(a: __m128, b: __m128) -> __m128 {
                    result!()
                }
                fn addsubpd(a: __m128d, b: __m128d) -> __m128d {
                    result!()
                }
                fn haddpd(a: __m128d, b: __m128d) -> __m128d {
                    result!()
                }
                fn haddps(a: __m128, b: __m128) -> __m128 {
                    result!()
                }
                fn hsubpd(a: __m128d, b: __m128d) -> __m128d {
                    result!()
                }
                fn hsubps(a: __m128, b: __m128) -> __m128 {
                    result!()
                }
                fn lddqu(mem_addr: *const i8) -> i8x16 {
                    result!()
                }
            }

            pub mod ssse3 {
                type i8x16 = [i8; 16];
                type i8x32 = [i8; 32];
                type i16x8 = [i16; 8];
                type i16x16 = [i16; 16];
                type i32x4 = [i32; 4];
                type i32x8 = [i32; 8];
                type i64x2 = [i64; 2];
                type i64x4 = [i64; 4];
                type u8x16 = [u8; 16];
                type u8x32 = [u8; 32];
                type u16x8 = [u16; 8];
                type u16x16 = [u16; 16];
                type u32x4 = [u32; 4];
                type u32x8 = [u32; 8];
                type u64x2 = [u64; 2];
                type u64x4 = [u64; 4];

                fn pabsb128(a: i8x16) -> u8x16 {
                    result!()
                }
                fn pabsw128(a: i16x8) -> u16x8 {
                    result!()
                }
                fn pabsd128(a: i32x4) -> u32x4 {
                    result!()
                }
                fn pshufb128(a: u8x16, b: u8x16) -> u8x16 {
                    result!()
                }
                fn phaddw128(a: i16x8, b: i16x8) -> i16x8 {
                    result!()
                }
                fn phaddsw128(a: i16x8, b: i16x8) -> i16x8 {
                    result!()
                }
                fn phaddd128(a: i32x4, b: i32x4) -> i32x4 {
                    result!()
                }
                fn phsubw128(a: i16x8, b: i16x8) -> i16x8 {
                    result!()
                }
                fn phsubsw128(a: i16x8, b: i16x8) -> i16x8 {
                    result!()
                }
                fn phsubd128(a: i32x4, b: i32x4) -> i32x4 {
                    result!()
                }
                fn pmaddubsw128(a: u8x16, b: i8x16) -> i16x8 {
                    result!()
                }
                fn pmulhrsw128(a: i16x8, b: i16x8) -> i16x8 {
                    result!()
                }
                fn psignb128(a: i8x16, b: i8x16) -> i8x16 {
                    result!()
                }
                fn psignw128(a: i16x8, b: i16x8) -> i16x8 {
                    result!()
                }
                fn psignd128(a: i32x4, b: i32x4) -> i32x4 {
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

        pub fn write() -> Result {
            result!()
        }
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
            default_contract!(add_with_overflow__i128);
            default_contract!(add_with_overflow__u128);

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
            default_contract!(sub_with_overflow__i128);
            default_contract!(sub_with_overflow__u128);

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
            default_contract!(wrapping_add__i128);
            default_contract!(wrapping_add__u128);

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
            default_contract!(wrapping_sub__i128);
            default_contract!(wrapping_sub__u128);

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
            default_contract!(wrapping_mul__i128);
            default_contract!(wrapping_mul__u128);

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
            default_contract!(saturating_add__i128);
            default_contract!(saturating_add__u128);

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
            pub mod map_fold {
                default_contract!(closure);
            }
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
            pub fn from_str_radix(src: &str, radix: u32) -> Result<u8, std::num::ParseIntError> {
                result!()
            }

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
            default_contract!(from_str);
            default_contract!(from_str_radix);

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
        pub mod implement_3 {
            pub mod cloned {
                default_contract!(closure);
            }
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

        pub mod index {
            pub fn slice_end_index_len_fail(index: usize, len: usize) {
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

            pub fn slice_start_index_len_fail(index: usize, len: usize) {
                panic!(
                    "range start index {} out of range for slice of length {}",
                    index, len
                );
            }

            pub fn slice_start_index_overflow_fail() -> ! {
                panic!("attempted to index slice from after maximum usize");
            }

            pub fn slice_end_index_overflow_fail() -> ! {
                panic!("attempted to index slice up to maximum usize");
            }
        }

        pub mod memchr {
            default_contract!(memchr);
        }
    }

    pub mod str {
        pub mod converts {
            pub fn from_utf8(v: &[u8]) -> Result<&str, core::str::Utf8Error> {
                result!()
            }
        }

        pub mod implement {
            pub fn trim(_self: &str) -> &str {
                result!()
            }
        }

        pub mod implement_ref_str {
            pub fn default() -> &'static str {
                ""
            }
        }

        pub mod pattern {
            pub mod implement_core_str_pattern_StrSearcher {
                use core::str::pattern::StrSearcher;

                pub fn new<'a, 'b>(haystack: &'a str, needle: &'b str) -> StrSearcher<'a, 'b> {
                    result!()
                }

                pub fn next_match<T>() -> T {
                    result!()
                }
            }

            pub mod implement_core_str_pattern_TwoWaySearcher {
                pub fn next<T>() -> T {
                    result!()
                }
            }

            pub mod Searcher {
                default_contract!(next_reject);
            }
        }

        pub fn slice_error_fail(s: &str, begin: usize, end: usize) -> ! {
            panic!("byte index is not a char boundary");
        }
    }

    pub mod unicode {
        pub mod unicode_data {
            pub mod white_space {
                pub fn lookup(c: char) -> bool {
                    result!()
                }
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

pub mod crossbeam_epoch {
    pub mod internal {
        pub mod implement_crossbeam_epoch_internal_Local {
            default_contract!(defer);
        }
    }
    pub mod sync {
        pub mod list {
            pub mod implement_crossbeam_epoch_sync_list_List_generic_par_T_generic_par_C {
                default_contract!(insert);
            }
        }
        pub mod queue {
            pub mod implement_crossbeam_epoch_sync_queue_Queue_generic_par_T {
                default_contract!(push);
            }
        }
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
        pub mod implement_hashbrown_raw_RawTable_generic_par_T {
            default_contract!(rehash_in_place);
            default_contract!(resize);
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

pub mod parking_lot {
    pub mod condvar {
        pub mod implement_parking_lot_condvar_Condvar {
            default_contract!(notify_all_slow);
            default_contract!(wait_until_internal);
        }
    }
    pub mod raw_mutex {
        pub mod implement_parking_lot_raw_mutex_RawMutex {
            default_contract!(lock_slow);
        }
    }
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

pub mod regex_syntax {
    pub mod ast {
        pub mod parse {
            pub mod implement_regex_syntax_ast_parse_ParserI_generic_par_P {
                default_contract!(bump_space);
                default_contract!(parse_octal);
                default_contract!(parse_hex_digits);
                default_contract!(parse_hex_brace);
                default_contract!(parse_unicode_class);
            }
        }
    }
}

pub mod rustc_data_structures {
    pub mod profiling {
        pub mod implement {
            pub mod instant_query_event {
                default_contract!(closure);
            }
        }
    }
}

pub mod rustc_errors {
    pub mod diagnostic {
        pub mod implement_rustc_errors_diagnostic_Diagnostic {
            default_contract!(message);
        }
        pub mod implement_rustc_errors_diagnostic_SubDiagnostic {
            default_contract!(message);
        }
    }
    pub mod implement_rustc_errors_Handler {
        default_contract!(emit_diagnostic);
    }
}

pub mod rustc_hir {
    pub mod hir {
        pub mod implement_rustc_hir_hir_VisibilityKind {
            default_contract!(is_pub);
        }
    }
}

pub mod rustc_middle {
    pub mod dep_graph {
        pub mod dep_node {
            pub mod implement_rustc_span_def_id_CrateNum {
                default_contract!(to_fingerprint);
            }
        }
        pub mod implement {
            default_contract!(is_eval_always);
        }

        pub mod implement_rustc_middle_ty_context_TyCtxt {
            default_contract!(diagnostic);
            default_contract!(has_errors_or_delayed_span_bugs);
            default_contract!(load_diagnostics);
            default_contract!(profiler);
            default_contract!(store_diagnostics);
            default_contract!(store_diagnostics_for_anon_node);
            default_contract!(try_force_from_dep_node);
        }
    }
    pub mod hir {
        pub mod implement_rustc_hir_hir_VisibilityKind {
            default_contract!(is_pub);
        }
        pub mod map {
            pub mod implement_rustc_middle_hir_map_Map {
                default_contract!(get_if_local);
            }
        }
    }
    pub mod infer {
        pub mod canonical {
            pub mod implement_rustc_middle_infer_canonical_Canonical_generic_par_V {
                default_contract!(clone);
            }
        }
    }
    pub mod ty {
        pub mod context {
            pub mod implement {
                default_contract!(intern_ty);
            }
            pub mod implement_rustc_middle_ty_context_TyCtxt {
                default_contract!(def_path);
                default_contract!(intern_existential_predicates);
                default_contract!(intern_substs);
                default_contract!(intern_type_list);
                default_contract!(mk_const);
            }
            pub mod tls {
                pub mod TLV {
                    default_contract!(__getit);
                }
            }
        }
        pub mod erase_regions {
            pub mod implement_rustc_middle_ty_erase_regions_RegionEraserVisitor {
                default_contract!(fold_region);
                default_contract!(fold_ty);
                default_contract!(tcx);
            }
        }
        pub mod fold {
            pub mod implement_rustc_middle_ty_fold_BoundVarReplacer {
                default_contract!(fold_const);
                default_contract!(fold_region);
                default_contract!(fold_ty);
                default_contract!(tcx);
            }
            pub mod implement_rustc_middle_ty_fold_HasEscapingVarsVisitor {
                default_contract!(visit_const);
                default_contract!(visit_region);
                default_contract!(visit_ty);
            }
            pub mod implement_rustc_middle_ty_fold_HasTypeFlagsVisitor {
                default_contract!(visit_const);
                default_contract!(visit_region);
                default_contract!(visit_ty);
            }
        }
        pub mod implement_rustc_middle_traits_Reveal {
            default_contract!(into_usize);
        }
        pub mod implement_rustc_middle_ty_context_TyCtxt {
            default_contract!(parent);
        }
        pub mod implement_rustc_middle_ty_FieldDef {
            default_contract!(ty);
        }
        pub mod normalize_erasing_regions {
            pub mod implement_rustc_middle_ty_normalize_erasing_regions_NormalizeAfterErasingRegionsFolder {
                default_contract!(fold_const);
                default_contract!(fold_ty);
                default_contract!(tcx);
            }
        }
        pub mod query {
            pub mod implement_rustc_middle_ty_query_Query {
                default_contract!(clone);
            }
            pub mod plumbing {
                pub mod implement {
                    default_contract!(current_query_job);
                    default_contract!(dep_graph);
                    default_contract!(incremental_verify_ich);
                    default_contract!(try_collect_active_jobs);
                }
            }
        }
        pub mod sty {
            pub mod implement_rustc_middle_ty_sty_Binder_ref_rustc_middle_ty_list_List_rustc_middle_ty_sty_ExistentialPredicate {
                default_contract!(principal);
            }
            pub mod implement_rustc_middle_ty_sty_ClosureSubsts {
                default_contract!(split);
            }
            pub mod implement_rustc_middle_ty_sty_FnSig {
                default_contract!(inputs);
                default_contract!(output);
            }
            pub mod implement_rustc_middle_ty_sty_ProjectionTy {
                default_contract!(self_ty);
            }
            pub mod implement_rustc_middle_ty_TyS {
                default_contract!(tuple_fields);
            }
        }
        pub mod subst {
            pub mod implement_rustc_middle_ty_list_List_rustc_middle_ty_subst_GenericArg {
                default_contract!(as_closure);
                default_contract!(as_generator);
            }
            pub mod implement_rustc_middle_ty_subst_GenericArg {
                default_contract!(expect_const);
                default_contract!(expect_ty);
                default_contract!(from);
            }
        }
    }
}

pub mod rustc_query_system {
    pub mod dep_graph {
        pub mod dep_node {
            pub mod implement {
                default_contract!(construct);
            }
        }
        pub mod graph {
            pub mod implement_3 {
                pub mod with_task_impl {
                    default_contract!(closure);
                }
            }
            pub mod implement_rustc_query_system_dep_graph_graph_DepGraph_generic_par_K {
                default_contract!(with_task_impl);
            }
            pub mod implement_rustc_query_system_dep_graph_graph_DepNodeColorMap {
                default_contract!(insert);
            }
        }
        pub mod serialized {
            pub mod implement_rustc_query_system_dep_graph_serialized_SerializedDepNodeIndex {
                default_contract!(clone);
            }
        }
    }
    pub mod query {
        pub mod config {
            pub mod implement {
                default_contract!(cache_on_disk);
                default_contract!(compute);
                default_contract!(handle_cycle_error);
                default_contract!(hash_result);
                default_contract!(try_load_from_disk);
            }
        }
        pub mod job {
            pub mod implement_rustc_query_system_query_job_QueryLatch_generic_par_CTX {
                default_contract!(find_cycle_in_stack);
            }
        }
        pub mod plumbing {
            default_contract!(incremental_verify_ich);
        }
    }
}

pub mod rustc_session {
    pub mod config {
        pub mod implement_rustc_session_config_ErrorOutputType {
            default_contract!(default);
        }
    }
    pub mod session {
        default_contract!(early_error);
    }
}

pub mod rustc_span {
    pub mod fatal_error {
        pub mod implement_rustc_span_fatal_error_FatalError {
            pub fn raise() {
                panic!("rust compiler fatal error");
            }
        }
    }
    pub mod implement_rustc_span_span_encoding_Span {
        default_contract!(partial_cmp);
        default_contract!(source_callsite);
    }
    pub mod source_map {
        pub mod implement_rustc_span_source_map_SourceMap {
            default_contract!(span_to_string);
        }
    }
    pub mod symbol {
        pub mod implement_rustc_span_symbol_Symbol {
            default_contract!(as_str);
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

pub mod shellwords {
    default_contract!(split);
}

pub mod stacker {
    default_contract!(_grow);
    default_contract!(remaining_stack);
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

                #[allow(deprecated)]
                pub mod implement_std_collections_hash_map_DefaultHasher {
                    use std::hash::SipHasher13;
                    pub struct DefaultHasher(SipHasher13);
                    pub fn new() -> DefaultHasher {
                        DefaultHasher(SipHasher13::new_with_keys(0, 0))
                    }
                }
            }
        }
    }

    pub mod env {
        pub fn _var_os() -> Option<std::ffi::OsString> {
            result!()
        }
    }

    pub mod ffi {
        pub mod c_str {
            pub mod implement_ref_str {
                pub mod new {
                    pub mod implement_ref_str {
                        default_contract!(into_vec);
                    }
                }
            }
            pub mod implement_std_ffi_c_str_CString {
                default_contract!(into_inner);
                default_contract!(_new);
            }
        }
        pub mod os_str {
            pub mod implement_std_ffi_os_str_OsStr {
                pub struct Slice {
                    pub inner: [u8],
                }
                pub struct OsStr {
                    inner: Slice,
                }
                pub struct Buf {
                    pub inner: Vec<u8>,
                }
                pub struct OsString {
                    inner: Buf,
                }

                pub fn to_os_string(_self: &OsStr) -> OsString {
                    OsString {
                        inner: Buf {
                            inner: _self.inner.inner.to_owned(),
                        },
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

    pub mod fs {
        pub mod implement_std_fs_File {
            use std::fs::File;

            pub fn read(_self: &mut File, buf: &mut [u8]) -> std::io::Result<usize> {
                result!()
            }

            pub fn seek(_self: &mut File, pos: std::io::SeekFrom) -> std::io::Result<u64> {
                result!()
            }
        }

        pub mod implement_std_fs_OpenOptions {
            use std::fs::{File, OpenOptions};
            use std::io::Result;
            use std::path::Path;

            pub fn append(_self: &OpenOptions, _: bool) -> &OpenOptions {
                _self
            }

            pub fn create(_self: &OpenOptions, _: bool) -> &OpenOptions {
                _self
            }

            pub fn create_new(_self: &OpenOptions, _: bool) -> &OpenOptions {
                _self
            }

            fn new() -> OpenOptions {
                result!()
            }

            fn _open(_self: &OpenOptions, path: &Path) -> Result<File> {
                result!()
            }

            pub fn read(_self: &OpenOptions, _: bool) -> &OpenOptions {
                _self
            }

            pub fn truncate(_self: &OpenOptions, _: bool) -> &OpenOptions {
                _self
            }

            pub fn write(_self: &OpenOptions, _: bool) -> &OpenOptions {
                _self
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
                default_contract!(new);
            }
        }
        pub mod stdio {
            use crate::foreign_contracts::core::fmt;
            pub fn _print(_args: fmt::Arguments<'_>) {}
        }
    }

    pub mod panicking {
        pub mod panic_count {
            default_contract!(is_zero_slow_path);
        }
    }

    pub mod path {

        pub mod implement_std_ffi_os_str_OsString {
            use std::ffi::OsStr;

            pub struct Path {
                inner: OsStr,
            }

            pub fn as_ref(_self: &Path) -> &OsStr {
                &_self.inner
            }
        }
        pub mod implement_std_path_Path {
            use std::ffi::OsString;
            use std::path::Path;

            pub struct PathBuf {
                inner: OsString,
            }

            pub fn as_ref(_self: &Path) -> &Path {
                _self
            }

            pub fn to_owned(_self: &Path) -> std::path::PathBuf {
                _self.to_path_buf()
            }
            pub fn clone_into(_self: &Path, target: &mut PathBuf) {
                _self.as_os_str().clone_into(&mut target.inner);
            }
        }

        pub mod implement_std_path_PathBuf {
            use std::ffi::OsString;
            use std::path::Path;

            pub struct PathBuf {
                inner: OsString,
            }
            fn default() -> std::path::PathBuf {
                std::path::PathBuf::new()
            }
            default_contract!(from_str);
            pub fn _push(_self: &mut PathBuf, path: &Path) {
                _self.inner.push(path);
            }
        }
    }

    pub mod result {}

    pub mod std_detect {
        pub mod detect {
            pub mod cache {
                pub fn test(bit: u32) -> bool {
                    result!()
                }
            }
        }
    }

    pub mod sys {
        pub mod unix {
            pub mod fast_thread_local {
                pub fn register_dtor() {}
            }

            pub mod memchr {
                pub fn memchr(_needle: u8, _haystack: &[u8]) -> Option<usize> {
                    result!()
                }
            }

            pub mod thread_local_dtor {
                default_contract!(register_dtor);
            }
        }
    }

    pub mod sys_common {
        pub mod mutex {
            pub mod implement_std_sys_common_mutex_MovableMutex {
                default_contract!(new);
            }
        }
    }

    pub mod thread {
        default_contract!(current);
        default_contract!(yield_now);
        pub mod implement_std_thread_Thread {
            default_contract!(id);
        }
        pub mod implement_std_thread_ThreadId {
            default_contract!(as_u64);
        }
        pub mod local {
            pub mod implement_std_thread_local_LocalKey_generic_par_T {
                default_contract!(try_with);
            }
        }
    }

    pub mod time {
        pub mod implement {
            default_contract!(elapsed);
            default_contract!(now);
        }
    }
}

pub mod tracing_core {
    pub mod callsite {
        default_contract!(register);
    }

    pub mod dispatcher {
        default_contract!(get_global);
        pub mod CURRENT_STATE {
            default_contract!(__getit);
        }

        pub mod implement_tracing_core_dispatcher_Dispatch {
            default_contract!(clone);
            default_contract!(enabled);
            default_contract!(event);
            default_contract!(is);
        }
    }

    pub mod field {
        pub mod implement_tracing_core_field_FieldSet {
            default_contract!(iter);
            default_contract!(next);
        }
        pub mod implement_tracing_core_field_Iter {
            default_contract!(iter);
            default_contract!(next);
        }
    }

    pub mod metadata {
        pub mod implement {
            default_contract!(fields);
        }
    }
}
