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

    pub mod collections {
        pub mod btree {
            pub mod mem {
                pub mod replace {
                    pub mod implement {
                        pub fn drop() {
                            panic!("implicit drop of panic guard");
                        }
                    }
                }
            }
            pub mod node {
                pub enum LeftOrRight<T> {
                    Left(T),
                    Right(T),
                }

                pub mod implement_alloc_collections_btree_node_Handle_alloc_collections_btree_node_NodeRef_alloc_collections_btree_node_marker_Mut_generic_par_K_generic_par_V_alloc_collections_btree_node_marker_Leaf_alloc_collections_btree_node_marker_Edge {
                    default_contract!(insert);
                }

                pub mod marker {
                    pub mod BorrowType {
                        fn PERMITS_TRAVERSAL() -> bool {
                            true
                        }
                        fn PERMITS_TRAVERSAL__alloc_collections_btree_node_marker_Owned() -> bool {
                            false
                        }
                    }
                }
                const B: usize = 6;
                pub const CAPACITY: usize = 2 * B - 1;
                pub const MIN_LEN_AFTER_SPLIT: usize = B - 1;
                const KV_IDX_CENTER: usize = B - 1;
                const EDGE_IDX_LEFT_OF_CENTER: usize = B - 1;
                const EDGE_IDX_RIGHT_OF_CENTER: usize = B;

                fn splitpoint(edge_idx: usize) -> (usize, LeftOrRight<usize>) {
                    precondition!(edge_idx <= CAPACITY);
                    match edge_idx {
                        0..EDGE_IDX_LEFT_OF_CENTER => {
                            (KV_IDX_CENTER - 1, LeftOrRight::Left(edge_idx))
                        }
                        EDGE_IDX_LEFT_OF_CENTER => (KV_IDX_CENTER, LeftOrRight::Left(edge_idx)),
                        EDGE_IDX_RIGHT_OF_CENTER => (KV_IDX_CENTER, LeftOrRight::Right(0)),
                        _ => (
                            KV_IDX_CENTER + 1,
                            LeftOrRight::Right(edge_idx - (KV_IDX_CENTER + 1 + 1)),
                        ),
                    }
                }
            }
        }

        pub mod vec_deque {
            fn INITIAL_CAPACITY() -> usize {
                7
            }
            fn MINIMUM_CAPACITY() -> usize {
                1
            }
            fn MAXIMUM_ZST_CAPACITY() -> usize {
                1 << (usize::BITS - 1)
            }
        }
    }

    pub mod fmt {
        default_contract!(format);
    }

    pub mod raw_vec {
        pub fn capacity_overflow() {
            assume_unreachable!("capacity overflow");
        }

        pub mod implement {
            use std::ptr::Unique;

            pub struct RawVec<T> {
                ptr: Unique<T>,
                cap: usize,
            }

            pub fn NEW<T>() -> RawVec<T> {
                RawVec {
                    ptr: unsafe { Unique::new_unchecked(4 as *mut T) },
                    cap: 0,
                }
            }
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

    pub mod str {
        pub mod implement_str {
            default_contract!(to_lowercase);
            default_contract!(repeat);
            default_contract!(replace);
        }
    }

    pub mod string {
        pub mod implement {
            use std::borrow::Cow;

            pub fn from_utf8_lossy() -> Cow<'static, str> {
                result!()
            }
        }
        pub mod implement_alloc_boxed_Box_str_alloc_alloc_Global {
            fn from(s: String) -> String {
                s
            }
        }
        pub mod implement_alloc_vec_Vec_u8_alloc_alloc_Global {
            fn from(s: String) -> String {
                s
            }
        }
        pub mod implement_alloc_string_Drain {
            default_contract!(drop);
        }
        pub mod implement_alloc_string_String {
            pub fn clone<T: Copy>(_self: T) -> T {
                //todo: provide mirai helper that does a deep clone
                _self
            }
            fn from(s: String) -> String {
                s
            }
        }
    }

    pub mod sync {
        fn MAX_REFCOUNT() -> usize {
            (isize::MAX) as usize
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

            fn assert_failed(index: usize, len: usize) -> ! {
                panic!(
                    "insertion index (is {}) should be <= len (is {})",
                    index, len
                );
            }
        }
        pub mod SpecExtend {
            pub fn spec_extend() {}
        }
    }
}

pub mod bcs {
    pub fn MAX_SEQUENCE_LENGTH() -> usize {
        (1 << 31) - 1
    }
    pub fn MAX_CONTAINER_DEPTH() -> usize {
        500
    }
}

pub mod core {
    pub mod alloc {
        pub mod Allocator {
            pub fn alloc<T>(
                _self: T,
                layout: std::alloc::Layout,
            ) -> Result<(std::ptr::NonNull<u8>, usize), core::alloc::AllocError>
            where
                T: std::alloc::Allocator,
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
                T: std::alloc::Allocator,
            {
                unsafe {
                    let buf = std::alloc::alloc_zeroed(layout);
                    Ok((std::ptr::NonNull::<u8>::new_unchecked(buf), layout.size()))
                }
            }

            pub fn dealloc<T>(_self: T, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout)
            where
                T: std::alloc::Allocator,
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
                T: std::alloc::Allocator,
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

    pub mod char {
        pub mod implement_core_char_CaseMappingIter {
            default_contract!(new);
        }

        pub mod implement_core_char_ToLowercase {
            default_contract!(next);
            default_contract!(size_hint);
        }

        pub mod implement_core_char_ToUppercase {
            default_contract!(next);
            default_contract!(size_hint);
        }

        pub fn TAG_CONT() -> u8 {
            0b1000_0000
        }
        pub fn TAG_TWO_B() -> u8 {
            0b1100_0000
        }
        pub fn TAG_THREE_B() -> u8 {
            0b1110_0000
        }
        pub fn TAG_FOUR_B() -> u8 {
            0b1111_0000
        }
        pub fn MAX_ONE_B() -> u32 {
            0x80
        }
        pub fn MAX_TWO_B() -> u32 {
            0x800
        }
        pub fn MAX_THREE_B() -> u32 {
            0x10000
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

            default_contract!(clone__fn_core_clone_Clone_clone_tuple_2_diem_crypto_ed25519_Ed25519Signature_u8_tuple_1_ref_tuple_2_diem_crypto_ed25519_Ed25519Signature_u8);

            pub fn clone__tuple_2_alloc_rc_Rc_mirai_abstract_value_AbstractValue_alloc_rc_Rc_mirai_abstract_value_AbstractValue<
                T: Copy,
            >(
                _self: &(T, T),
            ) -> (T, T) {
                (_self.0, _self.1)
            }

            pub fn clone__tuple_2_alloc_string_String_qstring_QValue<T: Copy>(
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

    pub mod core_arch {
        pub mod simd_llvm {
            //pub fn simd_select_bitmask
            default_contract!(simd_eq);
            default_contract!(simd_ne);
            default_contract!(simd_lt);
            default_contract!(simd_le);
            default_contract!(simd_gt);
            default_contract!(simd_ge);
            default_contract!(simd_shuffle2);
            default_contract!(simd_shuffle4);
            default_contract!(simd_shuffle8);
            default_contract!(simd_shuffle16);
            default_contract!(simd_shuffle32);
            default_contract!(simd_shuffle64);
            default_contract!(simd_shuffle128);
            default_contract!(simd_insert);
            default_contract!(simd_extract);
            //pub fn simd_select
            default_contract!(simd_bitmask);
            default_contract!(simd_cast);
            default_contract!(simd_add);
            default_contract!(simd_sub);
            default_contract!(simd_mul);
            default_contract!(simd_div);
            default_contract!(simd_shl);
            default_contract!(simd_shr);
            default_contract!(simd_and);
            default_contract!(simd_or);
            default_contract!(simd_xor);
            default_contract!(simd_saturating_add);
            default_contract!(simd_saturating_sub);
            default_contract!(simd_gather);
            // fn simd_scatter<T, U, V>(values: T, pointers: U, mask: V) {
            // }
            default_contract!(simd_reduce_add_unordered);
            default_contract!(simd_reduce_mul_unordered);
            default_contract!(simd_reduce_add_ordered);
            default_contract!(simd_reduce_mul_ordered);
            default_contract!(simd_reduce_min);
            default_contract!(simd_reduce_max);
            default_contract!(simd_reduce_min_nanless);
            default_contract!(simd_reduce_max_nanless);
            default_contract!(simd_reduce_and);
            default_contract!(simd_reduce_or);
            default_contract!(simd_reduce_xor);
            default_contract!(simd_reduce_all);
            default_contract!(simd_reduce_any);
            default_contract!(simd_select);
            default_contract!(simd_select_bitmask);
            default_contract!(simd_fmin);
            default_contract!(simd_fmax);
            default_contract!(simd_fsqrt);
            default_contract!(simd_fsin);
            default_contract!(simd_fcos);
            default_contract!(simd_fabs);
            default_contract!(simd_floor);
            default_contract!(simd_ceil);
            default_contract!(simd_fexp);
            default_contract!(simd_fexp2);
            default_contract!(simd_flog10);
            default_contract!(simd_flog2);
            default_contract!(simd_flog);
            //pub fn simd_fpowi
            //pub fn simd_fpow
            default_contract!(simd_fma);
        }

        #[cfg(target_arch = "x86_64")]
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

                default_contract!(addsubpd256);
                default_contract!(addsubps256);
                default_contract!(roundpd256);
                default_contract!(roundps256);
                default_contract!(sqrtps256);
                default_contract!(vblendvpd);
                default_contract!(vblendvps);
                default_contract!(vdpps);
                default_contract!(vhaddpd);
                default_contract!(vhaddps);
                default_contract!(vhsubpd);
                default_contract!(vhsubps);
                default_contract!(vcmppd);
                default_contract!(vcmppd256);
                default_contract!(vcmpps);
                default_contract!(vcmpps256);
                default_contract!(vcmpsd);
                default_contract!(vcmpss);
                default_contract!(vcvtdq2ps);
                default_contract!(vcvtpd2ps);
                default_contract!(vcvtps2dq);
                default_contract!(vcvttpd2dq);
                default_contract!(vcvtpd2dq);
                default_contract!(vcvttps2dq);
                default_contract!(vzeroall);
                default_contract!(vzeroupper);
                default_contract!(vpermilps256);
                default_contract!(vpermilps);
                default_contract!(vpermilpd256);
                default_contract!(vpermilpd);
                default_contract!(vperm2f128ps256);
                default_contract!(vperm2f128pd256);
                default_contract!(vperm2f128si256);
                default_contract!(vbroadcastf128ps256);
                default_contract!(vbroadcastf128pd256);
                fn storeupd256(mem_addr: *mut __m256d, a: __m256d) {
                    unsafe {
                        *mem_addr = a;
                    }
                }
                fn storeups256(mem_addr: *mut __m256, a: __m256) {
                    unsafe {
                        *mem_addr = a;
                    }
                }
                fn storeudq256(mem_addr: *mut i8x32, a: i8x32) {
                    unsafe {
                        *mem_addr = a;
                    }
                }
                default_contract!(maskloadpd256);
                default_contract!(maskstorepd256);
                default_contract!(maskloadpd);
                default_contract!(maskstorepd);
                default_contract!(maskloadps256);
                default_contract!(maskstoreps256);
                default_contract!(maskloadps);
                // fn maskstoreps(mem_addr: *mut i8, mask: i32x4, a: __m128) {
                //     result!()
                // }
                default_contract!(vlddqu);
                default_contract!(vrcpps);
                default_contract!(vrsqrtps);
                default_contract!(ptestz256);
                default_contract!(ptestc256);
                default_contract!(ptestnzc256);
                default_contract!(vtestzpd256);
                default_contract!(vtestcpd256);
                default_contract!(vtestnzcpd256);
                default_contract!(vtestzpd);
                default_contract!(vtestcpd);
                default_contract!(vtestnzcpd);
                default_contract!(vtestzps256);
                default_contract!(vtestcps256);
                default_contract!(vtestnzcps256);
                default_contract!(vtestzps);
                default_contract!(vtestcps);
                default_contract!(vtestnzcps);
                default_contract!(movmskpd256);
                default_contract!(movmskps256);
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

                default_contract!(pabsb);
                default_contract!(pabsw);
                default_contract!(pabsd);
                default_contract!(pavgb);
                default_contract!(pavgw);
                default_contract!(pblendvb);
                default_contract!(phaddw);
                default_contract!(phaddd);
                default_contract!(phaddsw);
                default_contract!(phsubw);
                default_contract!(phsubd);
                default_contract!(phsubsw);
                default_contract!(pmaddwd);
                default_contract!(pmaddubsw);
                default_contract!(maskloadd);
                default_contract!(maskloadd256);
                default_contract!(maskloadq);
                default_contract!(maskloadq256);
                // fn maskstored(mem_addr: *mut i8, mask: i32x4, a: i32x4) {
                //     result!()
                // }
                // fn maskstored256(mem_addr: *mut i8, mask: i32x8, a: i32x8) {
                //     result!()
                // }
                // fn maskstoreq(mem_addr: *mut i8, mask: i64x2, a: i64x2) {
                //     result!()
                // }
                // fn maskstoreq256(mem_addr: *mut i8, mask: i64x4, a: i64x4) {
                //     result!()
                // }
                default_contract!(pmaxsw);
                default_contract!(pmaxsd);
                default_contract!(pmaxsb);
                default_contract!(pmaxuw);
                default_contract!(pmaxud);
                default_contract!(pmaxub);
                default_contract!(pminsw);
                default_contract!(pminsd);
                default_contract!(pminsb);
                default_contract!(pminuw);
                default_contract!(pminud);
                default_contract!(pminub);
                default_contract!(pmovmskb);
                default_contract!(mpsadbw);
                default_contract!(pmulhuw);
                default_contract!(pmulhw);
                default_contract!(pmuldq);
                default_contract!(pmuludq);
                default_contract!(pmulhrsw);
                default_contract!(packsswb);
                default_contract!(packssdw);
                default_contract!(packuswb);
                default_contract!(packusdw);
                default_contract!(psadbw);
                default_contract!(psignb);
                default_contract!(psignw);
                default_contract!(psignd);
                default_contract!(psllw);
                default_contract!(pslld);
                default_contract!(psllq);
                default_contract!(pslliw);
                default_contract!(psllid);
                default_contract!(pslliq);
                default_contract!(psllvd);
                default_contract!(psllvd256);
                default_contract!(psllvq);
                default_contract!(psllvq256);
                default_contract!(psraw);
                default_contract!(psrad);
                default_contract!(psraiw);
                default_contract!(psraid);
                default_contract!(psravd);
                default_contract!(psravd256);
                default_contract!(psrlw);
                default_contract!(psrld);
                default_contract!(psrlq);
                default_contract!(psrliw);
                default_contract!(psrlid);
                default_contract!(psrliq);
                default_contract!(psrlvd);
                default_contract!(psrlvd256);
                default_contract!(psrlvq);
                default_contract!(psrlvq256);
                default_contract!(pshufb);
                default_contract!(permd);
                default_contract!(permps);
                default_contract!(vperm2i128);
                default_contract!(pgatherdd);
                default_contract!(vpgatherdd);
                default_contract!(pgatherdq);
                default_contract!(vpgatherdq);
                default_contract!(pgatherqd);
                default_contract!(vpgatherqd);
                default_contract!(pgatherqq);
                default_contract!(vpgatherqq);
                default_contract!(pgatherdpd);
                default_contract!(vpgatherdpd);
                default_contract!(pgatherqpd);
                default_contract!(vpgatherqpd);
                default_contract!(pgatherdps);
                default_contract!(vpgatherdps);
                default_contract!(pgatherqps);
                default_contract!(vpgatherqps);
                default_contract!(vpslldq);
                default_contract!(vpsrldq);
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
                // fn clflush(p: *const u8) {}
                fn lfence() {}
                fn mfence() {}
                default_contract!(pavgb);
                default_contract!(pavgw);
                default_contract!(pmaddwd);
                default_contract!(pmaxsw);
                default_contract!(pmaxub);
                default_contract!(pminsw);
                default_contract!(pminub);
                default_contract!(pmulhw);
                default_contract!(pmulhuw);
                default_contract!(pmuludq);
                default_contract!(psadbw);
                default_contract!(pslliw);
                default_contract!(psllw);
                default_contract!(psllid);
                default_contract!(pslld);
                default_contract!(pslliq);
                default_contract!(psllq);
                default_contract!(psraiw);
                default_contract!(psraw);
                default_contract!(psraid);
                default_contract!(psrad);
                default_contract!(psrliw);
                default_contract!(psrlw);
                default_contract!(psrlid);
                default_contract!(psrld);
                default_contract!(psrliq);
                default_contract!(psrlq);
                default_contract!(cvtdq2ps);
                default_contract!(cvtps2dq);
                // fn maskmovdqu(a: i8x16, mask: i8x16, mem_addr: *mut i8) {
                //     result!()
                // }
                default_contract!(packsswb);
                default_contract!(packssdw);
                default_contract!(packuswb);
                default_contract!(pmovmskb);
                default_contract!(maxsd);
                default_contract!(maxpd);
                default_contract!(minsd);
                default_contract!(minpd);
                default_contract!(sqrtsd);
                default_contract!(sqrtpd);
                default_contract!(cmpsd);
                default_contract!(cmppd);
                default_contract!(comieqsd);
                default_contract!(comiltsd);
                default_contract!(comilesd);
                default_contract!(comigtsd);
                default_contract!(comigesd);
                default_contract!(comineqsd);
                default_contract!(ucomieqsd);
                default_contract!(ucomiltsd);
                default_contract!(ucomilesd);
                default_contract!(ucomigtsd);
                default_contract!(ucomigesd);
                default_contract!(ucomineqsd);
                default_contract!(movmskpd);
                default_contract!(cvtpd2ps);
                default_contract!(cvtps2pd);
                default_contract!(cvtpd2dq);
                default_contract!(cvtsd2si);
                default_contract!(cvtsd2ss);
                default_contract!(cvtss2sd);
                default_contract!(cvttpd2dq);
                default_contract!(cvttsd2si);
                default_contract!(cvttps2dq);
                fn storeudq(mem_addr: *mut __m128i, a: __m128i) {
                    unsafe {
                        *mem_addr = a;
                    }
                }
                fn storeupd(mem_addr: *mut __m128d, a: __m128d) {
                    unsafe {
                        *mem_addr = a;
                    }
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

                default_contract!(addsubps);
                default_contract!(addsubpd);
                default_contract!(haddpd);
                default_contract!(haddps);
                default_contract!(hsubpd);
                default_contract!(hsubps);
                default_contract!(lddqu);
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

                default_contract!(pabsb128);
                default_contract!(pabsw128);
                default_contract!(pabsd128);
                default_contract!(pshufb128);
                default_contract!(phaddw128);
                default_contract!(phaddsw128);
                default_contract!(phaddd128);
                default_contract!(phsubw128);
                default_contract!(phsubsw128);
                default_contract!(phsubd128);
                default_contract!(pmaddubsw128);
                default_contract!(pmulhrsw128);
                default_contract!(psignb128);
                default_contract!(psignw128);
                default_contract!(psignd128);
            }
        }

        pub mod x86_64 {
            pub mod adx {
                default_contract!(llvm_addcarry_u64);
                default_contract!(llvm_subborrow_u64);
            }
        }
    }

    pub mod default {
        pub mod Default {
            default_contract!(default);
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

        pub mod builders {
            pub mod implement_core_fmt_builders_DebugStruct {
                default_contract!(field);
                default_contract!(finish);
            }

            pub mod implement_core_fmt_builders_DebugTuple {
                default_contract!(field);
                default_contract!(finish);
            }
        }

        pub mod float {
            pub mod implement_f32 {
                default_contract!(fmt);
            }
            pub mod implement_f64 {
                default_contract!(fmt);
            }
            pub mod implement_i128 {
                default_contract!(fmt);
            }
        }

        pub mod implement_core_fmt_Arguments {
            default_contract!(fmt);
        }

        pub mod implement_core_fmt_Formatter {
            default_contract!(debug_lower_hex);
            default_contract!(debug_struct);
            default_contract!(debug_tuple);
            default_contract!(new);
            default_contract!(write_fmt);
            default_contract!(write_str);
        }

        pub mod implement_str {
            default_contract!(fmt);
        }

        pub mod num {
            pub mod implement_i128 {
                default_contract!(fmt);
            }
            pub mod implement_u64 {
                default_contract!(fmt);
            }
        }

        pub mod rt {
            pub mod v1 {
                pub struct Argument {}
            }
        }

        pub struct Void {}

        default_contract!(write);
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
        pub mod foreign {
            // pub unsafe fn atomic_cxchg_seqcst_seqcst<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            //     if abstract_value!(true) {
            //         *dst = src;
            //         (old, true)
            //     } else {
            //         (*dst, false)
            //     }
            // }
            atomic_cxchg!(atomic_cxchg_seqcst_seqcst__i8, i8);
            atomic_cxchg!(atomic_cxchg_seqcst_seqcst__i16, i16);
            atomic_cxchg!(atomic_cxchg_seqcst_seqcst__i32, i32);
            atomic_cxchg!(atomic_cxchg_seqcst_seqcst__i64, i64);
            atomic_cxchg!(atomic_cxchg_seqcst_seqcst__isize, isize);
            atomic_cxchg!(atomic_cxchg_seqcst_seqcst__u8, u8);
            atomic_cxchg!(atomic_cxchg_seqcst_seqcst__u16, u16);
            atomic_cxchg!(atomic_cxchg_seqcst_seqcst__u32, u32);
            atomic_cxchg!(atomic_cxchg_seqcst_seqcst__u64, u64);
            atomic_cxchg!(atomic_cxchg_seqcst_seqcst, usize);
            atomic_cxchg!(atomic_cxchg_seqcst_seqcst__i128, i128);
            atomic_cxchg!(atomic_cxchg_seqcst_seqcst__u128, u128);

            // pub unsafe fn atomic_cxchg_acquire_acquire<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            //     if abstract_value!(true) {
            //         *dst = src;
            //         (old, true)
            //     } else {
            //         (*dst, false)
            //     }
            // }
            atomic_cxchg!(atomic_cxchg_acquire_acquire__i8, i8);
            atomic_cxchg!(atomic_cxchg_acquire_acquire__i16, i16);
            atomic_cxchg!(atomic_cxchg_acquire_acquire__i32, i32);
            atomic_cxchg!(atomic_cxchg_acquire_acquire__i64, i64);
            atomic_cxchg!(atomic_cxchg_acquire_acquire__isize, isize);
            atomic_cxchg!(atomic_cxchg_acquire_acquire__u8, u8);
            atomic_cxchg!(atomic_cxchg_acquire_acquire__u16, u16);
            atomic_cxchg!(atomic_cxchg_acquire_acquire__u32, u32);
            atomic_cxchg!(atomic_cxchg_acquire_acquire__u64, u64);
            atomic_cxchg!(atomic_cxchg_acquire_acquire, usize);
            atomic_cxchg!(atomic_cxchg_acquire_acquire__i128, i128);
            atomic_cxchg!(atomic_cxchg_acquire_acquire__u128, u128);

            // pub unsafe fn atomic_cxchg_release_relaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            //     if abstract_value!(true) {
            //         *dst = src;
            //         (old, true)
            //     } else {
            //         (*dst, false)
            //     }
            // }
            atomic_cxchg!(atomic_cxchg_release_relaxed__i8, i8);
            atomic_cxchg!(atomic_cxchg_release_relaxed__i16, i16);
            atomic_cxchg!(atomic_cxchg_release_relaxed__i32, i32);
            atomic_cxchg!(atomic_cxchg_release_relaxed__i64, i64);
            atomic_cxchg!(atomic_cxchg_release_relaxed__isize, isize);
            atomic_cxchg!(atomic_cxchg_release_relaxed__u8, u8);
            atomic_cxchg!(atomic_cxchg_release_relaxed__u16, u16);
            atomic_cxchg!(atomic_cxchg_release_relaxed__u32, u32);
            atomic_cxchg!(atomic_cxchg_release_relaxed__u64, u64);
            atomic_cxchg!(atomic_cxchg_release_relaxed, usize);
            atomic_cxchg!(atomic_cxchg_release_relaxed__i128, i128);
            atomic_cxchg!(atomic_cxchg_release_relaxed__u128, u128);

            // pub unsafe fn atomic_cxchg_acqrel_acquire<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            //     if abstract_value!(true) {
            //         *dst = src;
            //         (old, true)
            //     } else {
            //         (*dst, false)
            //     }
            // }
            atomic_cxchg!(atomic_cxchg_acqrel_acquire__i8, i8);
            atomic_cxchg!(atomic_cxchg_acqrel_acquire__i16, i16);
            atomic_cxchg!(atomic_cxchg_acqrel_acquire__i32, i32);
            atomic_cxchg!(atomic_cxchg_acqrel_acquire__i64, i64);
            atomic_cxchg!(atomic_cxchg_acqrel_acquire__isize, isize);
            atomic_cxchg!(atomic_cxchg_acqrel_acquire__u8, u8);
            atomic_cxchg!(atomic_cxchg_acqrel_acquire__u16, u16);
            atomic_cxchg!(atomic_cxchg_acqrel_acquire__u32, u32);
            atomic_cxchg!(atomic_cxchg_acqrel_acquire__u64, u64);
            atomic_cxchg!(atomic_cxchg_acqrel_acquire, usize);
            atomic_cxchg!(atomic_cxchg_acqrel_acquire__i128, i128);
            atomic_cxchg!(atomic_cxchg_acqrel_acquire__u128, u128);

            // pub unsafe fn atomic_cxchg_relaxed_relaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            //     if abstract_value!(true) {
            //         *dst = src;
            //         (old, true)
            //     } else {
            //         (*dst, false)
            //     }
            // }
            atomic_cxchg!(atomic_cxchg_relaxed_relaxed__i8, i8);
            atomic_cxchg!(atomic_cxchg_relaxed_relaxed__i16, i16);
            atomic_cxchg!(atomic_cxchg_relaxed_relaxed__i32, i32);
            atomic_cxchg!(atomic_cxchg_relaxed_relaxed__i64, i64);
            atomic_cxchg!(atomic_cxchg_relaxed_relaxed__isize, isize);
            atomic_cxchg!(atomic_cxchg_relaxed_relaxed__u8, u8);
            atomic_cxchg!(atomic_cxchg_relaxed_relaxed__u16, u16);
            atomic_cxchg!(atomic_cxchg_relaxed_relaxed__u32, u32);
            atomic_cxchg!(atomic_cxchg_relaxed_relaxed__u64, u64);
            atomic_cxchg!(atomic_cxchg_relaxed_relaxed, usize);
            atomic_cxchg!(atomic_cxchg_relaxed_relaxed__i128, i128);
            atomic_cxchg!(atomic_cxchg_relaxed_relaxed__u128, u128);

            // pub unsafe fn atomic_cxchg_seqcst_relaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            //     if abstract_value!(true) {
            //         *dst = src;
            //         (old, true)
            //     } else {
            //         (*dst, false)
            //     }
            // }
            atomic_cxchg!(atomic_cxchg_seqcst_relaxed__i8, i8);
            atomic_cxchg!(atomic_cxchg_seqcst_relaxed__i16, i16);
            atomic_cxchg!(atomic_cxchg_seqcst_relaxed__i32, i32);
            atomic_cxchg!(atomic_cxchg_seqcst_relaxed__i64, i64);
            atomic_cxchg!(atomic_cxchg_seqcst_relaxed__isize, isize);
            atomic_cxchg!(atomic_cxchg_seqcst_relaxed__u8, u8);
            atomic_cxchg!(atomic_cxchg_seqcst_relaxed__u16, u16);
            atomic_cxchg!(atomic_cxchg_seqcst_relaxed__u32, u32);
            atomic_cxchg!(atomic_cxchg_seqcst_relaxed__u64, u64);
            atomic_cxchg!(atomic_cxchg_seqcst_relaxed, usize);
            atomic_cxchg!(atomic_cxchg_seqcst_relaxed__i128, i128);
            atomic_cxchg!(atomic_cxchg_seqcst_relaxed__u128, u128);

            // pub unsafe fn atomic_cxchg_seqcst_acquire<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            //     if abstract_value!(true) {
            //         *dst = src;
            //         (old, true)
            //     } else {
            //         (*dst, false)
            //     }
            // }
            atomic_cxchg!(atomic_cxchg_seqcst_acquire__i8, i8);
            atomic_cxchg!(atomic_cxchg_seqcst_acquire__i16, i16);
            atomic_cxchg!(atomic_cxchg_seqcst_acquire__i32, i32);
            atomic_cxchg!(atomic_cxchg_seqcst_acquire__i64, i64);
            atomic_cxchg!(atomic_cxchg_seqcst_acquire__isize, isize);
            atomic_cxchg!(atomic_cxchg_seqcst_acquire__u8, u8);
            atomic_cxchg!(atomic_cxchg_seqcst_acquire__u16, u16);
            atomic_cxchg!(atomic_cxchg_seqcst_acquire__u32, u32);
            atomic_cxchg!(atomic_cxchg_seqcst_acquire__u64, u64);
            atomic_cxchg!(atomic_cxchg_seqcst_acquire, usize);
            atomic_cxchg!(atomic_cxchg_seqcst_acquire__i128, i128);
            atomic_cxchg!(atomic_cxchg_seqcst_acquire__u128, u128);

            // pub unsafe fn atomic_cxchg_acquire_relaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            //     if abstract_value!(true) {
            //         *dst = src;
            //         (old, true)
            //     } else {
            //         (*dst, false)
            //     }
            // }
            atomic_cxchg!(atomic_cxchg_acquire_relaxed__i8, i8);
            atomic_cxchg!(atomic_cxchg_acquire_relaxed__i16, i16);
            atomic_cxchg!(atomic_cxchg_acquire_relaxed__i32, i32);
            atomic_cxchg!(atomic_cxchg_acquire_relaxed__i64, i64);
            atomic_cxchg!(atomic_cxchg_acquire_relaxed__isize, isize);
            atomic_cxchg!(atomic_cxchg_acquire_relaxed__u8, u8);
            atomic_cxchg!(atomic_cxchg_acquire_relaxed__u16, u16);
            atomic_cxchg!(atomic_cxchg_acquire_relaxed__u32, u32);
            atomic_cxchg!(atomic_cxchg_acquire_relaxed__u64, u64);
            atomic_cxchg!(atomic_cxchg_acquire_relaxed, usize);
            atomic_cxchg!(atomic_cxchg_acquire_relaxed__i128, i128);
            atomic_cxchg!(atomic_cxchg_acquire_relaxed__u128, u128);

            // pub unsafe fn atomic_cxchg_acqrel_relaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            //     if abstract_value!(true) {
            //         *dst = src;
            //         (old, true)
            //     } else {
            //         (*dst, false)
            //     }
            // }
            atomic_cxchg!(atomic_cxchg_acqrel_relaxed__i8, i8);
            atomic_cxchg!(atomic_cxchg_acqrel_relaxed__i16, i16);
            atomic_cxchg!(atomic_cxchg_acqrel_relaxed__i32, i32);
            atomic_cxchg!(atomic_cxchg_acqrel_relaxed__i64, i64);
            atomic_cxchg!(atomic_cxchg_acqrel_relaxed__isize, isize);
            atomic_cxchg!(atomic_cxchg_acqrel_relaxed__u8, u8);
            atomic_cxchg!(atomic_cxchg_acqrel_relaxed__u16, u16);
            atomic_cxchg!(atomic_cxchg_acqrel_relaxed__u32, u32);
            atomic_cxchg!(atomic_cxchg_acqrel_relaxed__u64, u64);
            atomic_cxchg!(atomic_cxchg_acqrel_relaxed, usize);
            atomic_cxchg!(atomic_cxchg_acqrel_relaxed__i128, i128);
            atomic_cxchg!(atomic_cxchg_acqrel_relaxed__u128, u128);

            // pub unsafe fn atomic_cxchgweak_seqcst_seqcst<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            //     if abstract_value!(true) {
            //         *dst = src;
            //         (old, true)
            //     } else {
            //         (*dst, false)
            //     }
            // }
            atomic_cxchg!(atomic_cxchgweak_seqcst_seqcst__i8, i8);
            atomic_cxchg!(atomic_cxchgweak_seqcst_seqcst__i16, i16);
            atomic_cxchg!(atomic_cxchgweak_seqcst_seqcst__i32, i32);
            atomic_cxchg!(atomic_cxchgweak_seqcst_seqcst__i64, i64);
            atomic_cxchg!(atomic_cxchgweak_seqcst_seqcst__isize, isize);
            atomic_cxchg!(atomic_cxchgweak_seqcst_seqcst__u8, u8);
            atomic_cxchg!(atomic_cxchgweak_seqcst_seqcst__u16, u16);
            atomic_cxchg!(atomic_cxchgweak_seqcst_seqcst__u32, u32);
            atomic_cxchg!(atomic_cxchgweak_seqcst_seqcst__u64, u64);
            atomic_cxchg!(atomic_cxchgweak_seqcst_seqcst, usize);
            atomic_cxchg!(atomic_cxchgweak_seqcst_seqcst__i128, i128);
            atomic_cxchg!(atomic_cxchgweak_seqcst_seqcst__u128, u128);

            // pub unsafe fn atomic_cxchgweak_acquire_acquire<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            //     if abstract_value!(true) {
            //         *dst = src;
            //         (old, true)
            //     } else {
            //         (*dst, false)
            //     }
            // }
            atomic_cxchg!(atomic_cxchgweak_acquire_acquire__i8, i8);
            atomic_cxchg!(atomic_cxchgweak_acquire_acquire__i16, i16);
            atomic_cxchg!(atomic_cxchgweak_acquire_acquire__i32, i32);
            atomic_cxchg!(atomic_cxchgweak_acquire_acquire__i64, i64);
            atomic_cxchg!(atomic_cxchgweak_acquire_acquire__isize, isize);
            atomic_cxchg!(atomic_cxchgweak_acquire_acquire__u8, u8);
            atomic_cxchg!(atomic_cxchgweak_acquire_acquire__u16, u16);
            atomic_cxchg!(atomic_cxchgweak_acquire_acquire__u32, u32);
            atomic_cxchg!(atomic_cxchgweak_acquire_acquire__u64, u64);
            atomic_cxchg!(atomic_cxchgweak_acquire_acquire, usize);
            atomic_cxchg!(atomic_cxchgweak_acquire_acquire__i128, i128);
            atomic_cxchg!(atomic_cxchgweak_acquire_acquire__u128, u128);

            // pub unsafe fn atomic_cxchgweak_release_relaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            //     if abstract_value!(true) {
            //         *dst = src;
            //         (old, true)
            //     } else {
            //         (*dst, false)
            //     }
            // }
            atomic_cxchg!(atomic_cxchgweak_release_relaxed__i8, i8);
            atomic_cxchg!(atomic_cxchgweak_release_relaxed__i16, i16);
            atomic_cxchg!(atomic_cxchgweak_release_relaxed__i32, i32);
            atomic_cxchg!(atomic_cxchgweak_release_relaxed__i64, i64);
            atomic_cxchg!(atomic_cxchgweak_release_relaxed__isize, isize);
            atomic_cxchg!(atomic_cxchgweak_release_relaxed__u8, u8);
            atomic_cxchg!(atomic_cxchgweak_release_relaxed__u16, u16);
            atomic_cxchg!(atomic_cxchgweak_release_relaxed__u32, u32);
            atomic_cxchg!(atomic_cxchgweak_release_relaxed__u64, u64);
            atomic_cxchg!(atomic_cxchgweak_release_relaxed, usize);
            atomic_cxchg!(atomic_cxchgweak_release_relaxed__i128, i128);
            atomic_cxchg!(atomic_cxchgweak_release_relaxed__u128, u128);

            // pub unsafe fn atomic_cxchgweak_acqrel_acquire<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            //     if abstract_value!(true) {
            //         *dst = src;
            //         (old, true)
            //     } else {
            //         (*dst, false)
            //     }
            // }
            atomic_cxchg!(atomic_cxchgweak_acqrel_acquire__i8, i8);
            atomic_cxchg!(atomic_cxchgweak_acqrel_acquire__i16, i16);
            atomic_cxchg!(atomic_cxchgweak_acqrel_acquire__i32, i32);
            atomic_cxchg!(atomic_cxchgweak_acqrel_acquire__i64, i64);
            atomic_cxchg!(atomic_cxchgweak_acqrel_acquire__isize, isize);
            atomic_cxchg!(atomic_cxchgweak_acqrel_acquire__u8, u8);
            atomic_cxchg!(atomic_cxchgweak_acqrel_acquire__u16, u16);
            atomic_cxchg!(atomic_cxchgweak_acqrel_acquire__u32, u32);
            atomic_cxchg!(atomic_cxchgweak_acqrel_acquire__u64, u64);
            atomic_cxchg!(atomic_cxchgweak_acqrel_acquire, usize);
            atomic_cxchg!(atomic_cxchgweak_acqrel_acquire__i128, i128);
            atomic_cxchg!(atomic_cxchgweak_acqrel_acquire__u128, u128);

            // pub unsafe fn atomic_cxchgweak_relaxed_relaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            //     if abstract_value!(true) {
            //         *dst = src;
            //         (old, true)
            //     } else {
            //         (*dst, false)
            //     }
            // }
            atomic_cxchg!(atomic_cxchgweak_relaxed_relaxed__i8, i8);
            atomic_cxchg!(atomic_cxchgweak_relaxed_relaxed__i16, i16);
            atomic_cxchg!(atomic_cxchgweak_relaxed_relaxed__i32, i32);
            atomic_cxchg!(atomic_cxchgweak_relaxed_relaxed__i64, i64);
            atomic_cxchg!(atomic_cxchgweak_relaxed_relaxed__isize, isize);
            atomic_cxchg!(atomic_cxchgweak_relaxed_relaxed__u8, u8);
            atomic_cxchg!(atomic_cxchgweak_relaxed_relaxed__u16, u16);
            atomic_cxchg!(atomic_cxchgweak_relaxed_relaxed__u32, u32);
            atomic_cxchg!(atomic_cxchgweak_relaxed_relaxed__u64, u64);
            atomic_cxchg!(atomic_cxchgweak_relaxed_relaxed, usize);
            atomic_cxchg!(atomic_cxchgweak_relaxed_relaxed__i128, i128);
            atomic_cxchg!(atomic_cxchgweak_relaxed_relaxed__u128, u128);

            // pub unsafe fn atomic_cxchgweak_seqcst_relaxed<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            //     if abstract_value!(true) {
            //         *dst = src;
            //         (old, true)
            //     } else {
            //         (*dst, false)
            //     }
            // }
            atomic_cxchg!(atomic_cxchgweak_seqcst_relaxed__i8, i8);
            atomic_cxchg!(atomic_cxchgweak_seqcst_relaxed__i16, i16);
            atomic_cxchg!(atomic_cxchgweak_seqcst_relaxed__i32, i32);
            atomic_cxchg!(atomic_cxchgweak_seqcst_relaxed__i64, i64);
            atomic_cxchg!(atomic_cxchgweak_seqcst_relaxed__isize, isize);
            atomic_cxchg!(atomic_cxchgweak_seqcst_relaxed__u8, u8);
            atomic_cxchg!(atomic_cxchgweak_seqcst_relaxed__u16, u16);
            atomic_cxchg!(atomic_cxchgweak_seqcst_relaxed__u32, u32);
            atomic_cxchg!(atomic_cxchgweak_seqcst_relaxed__u64, u64);
            atomic_cxchg!(atomic_cxchgweak_seqcst_relaxed, usize);
            atomic_cxchg!(atomic_cxchgweak_seqcst_relaxed__i128, i128);
            atomic_cxchg!(atomic_cxchgweak_seqcst_relaxed__u128, u128);

            // pub unsafe fn atomic_cxchgweak_seqcst_acquire<T>(dst: *mut T, old: T, src: T) -> (T, bool) {
            //     if abstract_value!(true) {
            //         *dst = src;
            //         (old, true)
            //     } else {
            //         (*dst, false)
            //     }
            // }
            atomic_cxchg!(atomic_cxchgweak_seqcst_acquire__i8, i8);
            atomic_cxchg!(atomic_cxchgweak_seqcst_acquire__i16, i16);
            atomic_cxchg!(atomic_cxchgweak_seqcst_acquire__i32, i32);
            atomic_cxchg!(atomic_cxchgweak_seqcst_acquire__i64, i64);
            atomic_cxchg!(atomic_cxchgweak_seqcst_acquire__isize, isize);
            atomic_cxchg!(atomic_cxchgweak_seqcst_acquire__u8, u8);
            atomic_cxchg!(atomic_cxchgweak_seqcst_acquire__u16, u16);
            atomic_cxchg!(atomic_cxchgweak_seqcst_acquire__u32, u32);
            atomic_cxchg!(atomic_cxchgweak_seqcst_acquire__u64, u64);
            atomic_cxchg!(atomic_cxchgweak_seqcst_acquire, usize);
            atomic_cxchg!(atomic_cxchgweak_seqcst_acquire__i128, i128);
            atomic_cxchg!(atomic_cxchgweak_seqcst_acquire__u128, u128);

            // pub unsafe fn atomic_cxchgweak_acquire_relaxed<T>(
            //     dst: *mut T,
            //     old: T,
            //     src: T,
            // ) -> (T, bool) {
            //     if abstract_value!(true) {
            //         *dst = src;
            //         (old, true)
            //     } else {
            //         (*dst, false)
            //     }
            // }
            atomic_cxchg!(atomic_cxchgweak_acquire_relaxed__i8, i8);
            atomic_cxchg!(atomic_cxchgweak_acquire_relaxed__i16, i16);
            atomic_cxchg!(atomic_cxchgweak_acquire_relaxed__i32, i32);
            atomic_cxchg!(atomic_cxchgweak_acquire_relaxed__i64, i64);
            atomic_cxchg!(atomic_cxchgweak_acquire_relaxed__isize, isize);
            atomic_cxchg!(atomic_cxchgweak_acquire_relaxed__u8, u8);
            atomic_cxchg!(atomic_cxchgweak_acquire_relaxed__u16, u16);
            atomic_cxchg!(atomic_cxchgweak_acquire_relaxed__u32, u32);
            atomic_cxchg!(atomic_cxchgweak_acquire_relaxed__u64, u64);
            atomic_cxchg!(atomic_cxchgweak_acquire_relaxed, usize);
            atomic_cxchg!(atomic_cxchgweak_acquire_relaxed__i128, i128);
            atomic_cxchg!(atomic_cxchgweak_acquire_relaxed__u128, u128);

            // pub unsafe fn atomic_cxchgweak_acqrel_relaxed<T>(
            //     dst: *mut T,
            //     old: T,
            //     src: T,
            // ) -> (T, bool) {
            //     if abstract_value!(true) {
            //         *dst = src;
            //         (old, true)
            //     } else {
            //         (*dst, false)
            //     }
            // }
            atomic_cxchg!(atomic_cxchgweak_acqrel_relaxed__i8, i8);
            atomic_cxchg!(atomic_cxchgweak_acqrel_relaxed__i16, i16);
            atomic_cxchg!(atomic_cxchgweak_acqrel_relaxed__i32, i32);
            atomic_cxchg!(atomic_cxchgweak_acqrel_relaxed__i64, i64);
            atomic_cxchg!(atomic_cxchgweak_acqrel_relaxed__isize, isize);
            atomic_cxchg!(atomic_cxchgweak_acqrel_relaxed__u8, u8);
            atomic_cxchg!(atomic_cxchgweak_acqrel_relaxed__u16, u16);
            atomic_cxchg!(atomic_cxchgweak_acqrel_relaxed__u32, u32);
            atomic_cxchg!(atomic_cxchgweak_acqrel_relaxed__u64, u64);
            atomic_cxchg!(atomic_cxchgweak_acqrel_relaxed, usize);
            atomic_cxchg!(atomic_cxchgweak_acqrel_relaxed__i128, i128);
            atomic_cxchg!(atomic_cxchgweak_acqrel_relaxed__u128, u128);

            pub unsafe fn atomic_load_seqcst<T>(src: *const T) -> T
            where
                T: Copy,
            {
                *src
            }

            pub unsafe fn atomic_load_acquire<T>(src: *const T) -> T
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

            pub unsafe fn atomic_store_seqcst<T>(dst: *mut T, val: T)
            where
                T: Copy,
            {
                *dst = val;
            }

            pub unsafe fn atomic_store_release<T>(dst: *mut T, val: T)
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

            pub unsafe fn atomic_xchg_seqcst<T>(dst: *mut T, src: T) -> T
            where
                T: Copy,
            {
                let result = *dst;
                *dst = src;
                result
            }

            pub unsafe fn atomic_xchg_acquire<T>(dst: *mut T, src: T) -> T
            where
                T: Copy,
            {
                let result = *dst;
                *dst = src;
                result
            }

            pub unsafe fn atomic_xchg_release<T>(dst: *mut T, src: T) -> T
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
            // pub unsafe fn atomic_xadd_seqcst<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::AddAssign,
            // {
            //     let result = *dst;
            //     *dst += src;
            //     result
            // }
            atomic_int!(atomic_xadd_seqcst__i8, i8, +=);
            atomic_int!(atomic_xadd_seqcst__i16, i16, +=);
            atomic_int!(atomic_xadd_seqcst__i32, i32, +=);
            atomic_int!(atomic_xadd_seqcst__i64, i64, +=);
            atomic_int!(atomic_xadd_seqcst__isize, isize, +=);
            atomic_int!(atomic_xadd_seqcst__u8, u8, +=);
            atomic_int!(atomic_xadd_seqcst__u16, u16, +=);
            atomic_int!(atomic_xadd_seqcst__u32, u32, +=);
            atomic_int!(atomic_xadd_seqcst__u64, u64, +=);
            atomic_int!(atomic_xadd_seqcst__usize, usize, +=);
            atomic_int!(atomic_xadd_seqcst__i128, i128, +=);
            atomic_int!(atomic_xadd_seqcst__u128, u128, +=);

            // pub unsafe fn atomic_xadd_acquire<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::AddAssign,
            // {
            //     let result = *dst;
            //     *dst += src;
            //     result
            // }
            atomic_int!(atomic_xadd_acquire__i8, i8, +=);
            atomic_int!(atomic_xadd_acquire__i16, i16, +=);
            atomic_int!(atomic_xadd_acquire__i32, i32, +=);
            atomic_int!(atomic_xadd_acquire__i64, i64, +=);
            atomic_int!(atomic_xadd_acquire__isize, isize, +=);
            atomic_int!(atomic_xadd_acquire__u8, u8, +=);
            atomic_int!(atomic_xadd_acquire__u16, u16, +=);
            atomic_int!(atomic_xadd_acquire__u32, u32, +=);
            atomic_int!(atomic_xadd_acquire__u64, u64, +=);
            atomic_int!(atomic_xadd_acquire__usize, usize, +=);
            atomic_int!(atomic_xadd_acquire__i128, i128, +=);
            atomic_int!(atomic_xadd_acquire__u128, u128, +=);

            // pub unsafe fn atomic_xadd_release<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::AddAssign,
            // {
            //     let result = *dst;
            //     *dst += src;
            //     result
            // }
            atomic_int!(atomic_xadd_release__i8, i8, +=);
            atomic_int!(atomic_xadd_release__i16, i16, +=);
            atomic_int!(atomic_xadd_release__i32, i32, +=);
            atomic_int!(atomic_xadd_release__i64, i64, +=);
            atomic_int!(atomic_xadd_release__isize, isize, +=);
            atomic_int!(atomic_xadd_release__u8, u8, +=);
            atomic_int!(atomic_xadd_release__u16, u16, +=);
            atomic_int!(atomic_xadd_release__u32, u32, +=);
            atomic_int!(atomic_xadd_release__u64, u64, +=);
            atomic_int!(atomic_xadd_release__usize, usize, +=);
            atomic_int!(atomic_xadd_release__i128, i128, +=);
            atomic_int!(atomic_xadd_release__u128, u128, +=);

            // pub unsafe fn atomic_xadd_acqrel<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::AddAssign,
            // {
            //     let result = *dst;
            //     *dst += src;
            //     result
            // }
            atomic_int!(atomic_xadd_acqrel__i8, i8, +=);
            atomic_int!(atomic_xadd_acqrel__i16, i16, +=);
            atomic_int!(atomic_xadd_acqrel__i32, i32, +=);
            atomic_int!(atomic_xadd_acqrel__i64, i64, +=);
            atomic_int!(atomic_xadd_acqrel__isize, isize, +=);
            atomic_int!(atomic_xadd_acqrel__u8, u8, +=);
            atomic_int!(atomic_xadd_acqrel__u16, u16, +=);
            atomic_int!(atomic_xadd_acqrel__u32, u32, +=);
            atomic_int!(atomic_xadd_acqrel__u64, u64, +=);
            atomic_int!(atomic_xadd_acqrel__usize, usize, +=);
            atomic_int!(atomic_xadd_acqrel__i128, i128, +=);
            atomic_int!(atomic_xadd_acqrel__u128, u128, +=);

            // pub unsafe fn atomic_xadd_relaxed<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::AddAssign,
            // {
            //     let result = *dst;
            //     *dst += src;
            //     result
            // }
            atomic_int!(atomic_xadd_relaxed__i8, i8, +=);
            atomic_int!(atomic_xadd_relaxed__i16, i16, +=);
            atomic_int!(atomic_xadd_relaxed__i32, i32, +=);
            atomic_int!(atomic_xadd_relaxed__i64, i64, +=);
            atomic_int!(atomic_xadd_relaxed__isize, isize, +=);
            atomic_int!(atomic_xadd_relaxed__u8, u8, +=);
            atomic_int!(atomic_xadd_relaxed__u16, u16, +=);
            atomic_int!(atomic_xadd_relaxed__u32, u32, +=);
            atomic_int!(atomic_xadd_relaxed__u64, u64, +=);
            atomic_int!(atomic_xadd_relaxed__usize, usize, +=);
            atomic_int!(atomic_xadd_relaxed__i128, i128, +=);
            atomic_int!(atomic_xadd_relaxed__u128, u128, +=);

            // pub unsafe fn atomic_xsub_seqcst<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::SubAssign,
            // {
            //     let result = *dst;
            //     *dst -= src;
            //     result
            // }
            atomic_int!(atomic_xsub_seqcst__i8, i8, -=);
            atomic_int!(atomic_xsub_seqcst__i16, i16, -=);
            atomic_int!(atomic_xsub_seqcst__i32, i32, -=);
            atomic_int!(atomic_xsub_seqcst__i64, i64, -=);
            atomic_int!(atomic_xsub_seqcst__isize, isize, -=);
            atomic_int!(atomic_xsub_seqcst__u8, u8, -=);
            atomic_int!(atomic_xsub_seqcst__u16, u16, -=);
            atomic_int!(atomic_xsub_seqcst__u32, u32, -=);
            atomic_int!(atomic_xsub_seqcst__u64, u64, -=);
            atomic_int!(atomic_xsub_seqcst__usize, usize, -=);
            atomic_int!(atomic_xsub_seqcst__i128, i128, -=);
            atomic_int!(atomic_xsub_seqcst__u128, u128, -=);

            // pub unsafe fn atomic_xsub_acquire<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::SubAssign,
            // {
            //     let result = *dst;
            //     *dst -= src;
            //     result
            // }
            atomic_int!(atomic_xsub_acquire__i8, i8, -=);
            atomic_int!(atomic_xsub_acquire__i16, i16, -=);
            atomic_int!(atomic_xsub_acquire__i32, i32, -=);
            atomic_int!(atomic_xsub_acquire__i64, i64, -=);
            atomic_int!(atomic_xsub_acquire__isize, isize, -=);
            atomic_int!(atomic_xsub_acquire__u8, u8, -=);
            atomic_int!(atomic_xsub_acquire__u16, u16, -=);
            atomic_int!(atomic_xsub_acquire__u32, u32, -=);
            atomic_int!(atomic_xsub_acquire__u64, u64, -=);
            atomic_int!(atomic_xsub_acquire__usize, usize, -=);
            atomic_int!(atomic_xsub_acquire__i128, i128, -=);
            atomic_int!(atomic_xsub_acquire__u128, u128, -=);

            // pub unsafe fn atomic_xsub_release<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::SubAssign,
            // {
            //     let result = *dst;
            //     *dst -= src;
            //     result
            // }
            atomic_int!(atomic_xsub_release__i8, i8, -=);
            atomic_int!(atomic_xsub_release__i16, i16, -=);
            atomic_int!(atomic_xsub_release__i32, i32, -=);
            atomic_int!(atomic_xsub_release__i64, i64, -=);
            atomic_int!(atomic_xsub_release__isize, isize, -=);
            atomic_int!(atomic_xsub_release__u8, u8, -=);
            atomic_int!(atomic_xsub_release__u16, u16, -=);
            atomic_int!(atomic_xsub_release__u32, u32, -=);
            atomic_int!(atomic_xsub_release__u64, u64, -=);
            atomic_int!(atomic_xsub_release__usize, usize, -=);
            atomic_int!(atomic_xsub_release__i128, i128, -=);
            atomic_int!(atomic_xsub_release__u128, u128, -=);

            // pub unsafe fn atomic_xsub_acqrel<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::SubAssign,
            // {
            //     let result = *dst;
            //     *dst -= src;
            //     result
            // }
            atomic_int!(atomic_xsub_acqrel__i8, i8, -=);
            atomic_int!(atomic_xsub_acqrel__i16, i16, -=);
            atomic_int!(atomic_xsub_acqrel__i32, i32, -=);
            atomic_int!(atomic_xsub_acqrel__i64, i64, -=);
            atomic_int!(atomic_xsub_acqrel__isize, isize, -=);
            atomic_int!(atomic_xsub_acqrel__u8, u8, -=);
            atomic_int!(atomic_xsub_acqrel__u16, u16, -=);
            atomic_int!(atomic_xsub_acqrel__u32, u32, -=);
            atomic_int!(atomic_xsub_acqrel__u64, u64, -=);
            atomic_int!(atomic_xsub_acqrel__usize, usize, -=);
            atomic_int!(atomic_xsub_acqrel__i128, i128, -=);
            atomic_int!(atomic_xsub_acqrel__u128, u128, -=);

            // pub unsafe fn atomic_xsub_relaxed<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::SubAssign,
            // {
            //     let result = *dst;
            //     *dst -= src;
            //     result
            // }
            atomic_int!(atomic_xsub_relaxed__i8, i8, -=);
            atomic_int!(atomic_xsub_relaxed__i16, i16, -=);
            atomic_int!(atomic_xsub_relaxed__i32, i32, -=);
            atomic_int!(atomic_xsub_relaxed__i64, i64, -=);
            atomic_int!(atomic_xsub_relaxed__isize, isize, -=);
            atomic_int!(atomic_xsub_relaxed__u8, u8, -=);
            atomic_int!(atomic_xsub_relaxed__u16, u16, -=);
            atomic_int!(atomic_xsub_relaxed__u32, u32, -=);
            atomic_int!(atomic_xsub_relaxed__u64, u64, -=);
            atomic_int!(atomic_xsub_relaxed__usize, usize, -=);
            atomic_int!(atomic_xsub_relaxed__i128, i128, -=);
            atomic_int!(atomic_xsub_relaxed__u128, u128, -=);

            // pub unsafe fn atomic_and_seqcst<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::BitAndAssign,
            // {
            //     let result = *dst;
            //     *dst &= src;
            //     result
            // }
            atomic_int!(atomic_and_seqcst__i8, i8, &=);
            atomic_int!(atomic_and_seqcst__i16, i16, &=);
            atomic_int!(atomic_and_seqcst__i32, i32, &=);
            atomic_int!(atomic_and_seqcst__i64, i64, &=);
            atomic_int!(atomic_and_seqcst__isize, isize, &=);
            atomic_int!(atomic_and_seqcst__u8, u8, &=);
            atomic_int!(atomic_and_seqcst__u16, u16, &=);
            atomic_int!(atomic_and_seqcst__u32, u32, &=);
            atomic_int!(atomic_and_seqcst__u64, u64, &=);
            atomic_int!(atomic_and_seqcst__usize, usize, &=);
            atomic_int!(atomic_and_seqcst__i128, i128, &=);
            atomic_int!(atomic_and_seqcst__u128, u128, &=);

            // pub unsafe fn atomic_and_acquire<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::BitAndAssign,
            // {
            //     let result = *dst;
            //     *dst &= src;
            //     result
            // }
            atomic_int!(atomic_and_acquire__i8, i8, &=);
            atomic_int!(atomic_and_acquire__i16, i16, &=);
            atomic_int!(atomic_and_acquire__i32, i32, &=);
            atomic_int!(atomic_and_acquire__i64, i64, &=);
            atomic_int!(atomic_and_acquire__isize, isize, &=);
            atomic_int!(atomic_and_acquire__u8, u8, &=);
            atomic_int!(atomic_and_acquire__u16, u16, &=);
            atomic_int!(atomic_and_acquire__u32, u32, &=);
            atomic_int!(atomic_and_acquire__u64, u64, &=);
            atomic_int!(atomic_and_acquire__usize, usize, &=);
            atomic_int!(atomic_and_acquire__i128, i128, &=);
            atomic_int!(atomic_and_acquire__u128, u128, &=);

            // pub unsafe fn atomic_and_release<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::BitAndAssign,
            // {
            //     let result = *dst;
            //     *dst &= src;
            //     result
            // }
            atomic_int!(atomic_and_release__i8, i8, &=);
            atomic_int!(atomic_and_release__i16, i16, &=);
            atomic_int!(atomic_and_release__i32, i32, &=);
            atomic_int!(atomic_and_release__i64, i64, &=);
            atomic_int!(atomic_and_release__isize, isize, &=);
            atomic_int!(atomic_and_release__u8, u8, &=);
            atomic_int!(atomic_and_release__u16, u16, &=);
            atomic_int!(atomic_and_release__u32, u32, &=);
            atomic_int!(atomic_and_release__u64, u64, &=);
            atomic_int!(atomic_and_release__usize, usize, &=);
            atomic_int!(atomic_and_release__i128, i128, &=);
            atomic_int!(atomic_and_release__u128, u128, &=);

            // pub unsafe fn atomic_and_acqrel<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::BitAndAssign,
            // {
            //     let result = *dst;
            //     *dst &= src;
            //     result
            // }
            atomic_int!(atomic_and_acqrel__i8, i8, &=);
            atomic_int!(atomic_and_acqrel__i16, i16, &=);
            atomic_int!(atomic_and_acqrel__i32, i32, &=);
            atomic_int!(atomic_and_acqrel__i64, i64, &=);
            atomic_int!(atomic_and_acqrel__isize, isize, &=);
            atomic_int!(atomic_and_acqrel__u8, u8, &=);
            atomic_int!(atomic_and_acqrel__u16, u16, &=);
            atomic_int!(atomic_and_acqrel__u32, u32, &=);
            atomic_int!(atomic_and_acqrel__u64, u64, &=);
            atomic_int!(atomic_and_acqrel__usize, usize, &=);
            atomic_int!(atomic_and_acqrel__i128, i128, &=);
            atomic_int!(atomic_and_acqrel__u128, u128, &=);

            // pub unsafe fn atomic_and_relaxed<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::BitAndAssign,
            // {
            //     let result = *dst;
            //     *dst &= src;
            //     result
            // }
            atomic_int!(atomic_and_relaxed__i8, i8, &=);
            atomic_int!(atomic_and_relaxed__i16, i16, &=);
            atomic_int!(atomic_and_relaxed__i32, i32, &=);
            atomic_int!(atomic_and_relaxed__i64, i64, &=);
            atomic_int!(atomic_and_relaxed__isize, isize, &=);
            atomic_int!(atomic_and_relaxed__u8, u8, &=);
            atomic_int!(atomic_and_relaxed__u16, u16, &=);
            atomic_int!(atomic_and_relaxed__u32, u32, &=);
            atomic_int!(atomic_and_relaxed__u64, u64, &=);
            atomic_int!(atomic_and_relaxed__usize, usize, &=);
            atomic_int!(atomic_and_relaxed__i128, i128, &=);
            atomic_int!(atomic_and_relaxed__u128, u128, &=);

            // pub unsafe fn atomic_nand_seqcst<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            // {
            //     let result = *dst;
            //     *dst = abstract_value!(result);
            //     result
            // }
            atomic_nand!(atomic_nand_seqcst__i8, i8);
            atomic_nand!(atomic_nand_seqcst__i16, i16);
            atomic_nand!(atomic_nand_seqcst__i32, i32);
            atomic_nand!(atomic_nand_seqcst__i64, i64);
            atomic_nand!(atomic_nand_seqcst__isize, isize);
            atomic_nand!(atomic_nand_seqcst__u8, u8);
            atomic_nand!(atomic_nand_seqcst__u16, u16);
            atomic_nand!(atomic_nand_seqcst__u32, u32);
            atomic_nand!(atomic_nand_seqcst__u64, u64);
            atomic_nand!(atomic_nand_seqcst__usize, usize);
            atomic_nand!(atomic_nand_seqcst__i128, i128);
            atomic_nand!(atomic_nand_seqcst__u128, u128);

            // pub unsafe fn atomic_nand_acquire<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            // {
            //     let result = *dst;
            //     *dst = abstract_value!(result);
            //     result
            // }
            atomic_nand!(atomic_nand_acquire__i8, i8);
            atomic_nand!(atomic_nand_acquire__i16, i16);
            atomic_nand!(atomic_nand_acquire__i32, i32);
            atomic_nand!(atomic_nand_acquire__i64, i64);
            atomic_nand!(atomic_nand_acquire__isize, isize);
            atomic_nand!(atomic_nand_acquire__u8, u8);
            atomic_nand!(atomic_nand_acquire__u16, u16);
            atomic_nand!(atomic_nand_acquire__u32, u32);
            atomic_nand!(atomic_nand_acquire__u64, u64);
            atomic_nand!(atomic_nand_acquire__usize, usize);
            atomic_nand!(atomic_nand_acquire__i128, i128);
            atomic_nand!(atomic_nand_acquire__u128, u128);

            // pub unsafe fn atomic_nand_release<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            // {
            //     let result = *dst;
            //     *dst = abstract_value!(result);
            //     result
            // }
            atomic_nand!(atomic_nand_release__i8, i8);
            atomic_nand!(atomic_nand_release__i16, i16);
            atomic_nand!(atomic_nand_release__i32, i32);
            atomic_nand!(atomic_nand_release__i64, i64);
            atomic_nand!(atomic_nand_release__isize, isize);
            atomic_nand!(atomic_nand_release__u8, u8);
            atomic_nand!(atomic_nand_release__u16, u16);
            atomic_nand!(atomic_nand_release__u32, u32);
            atomic_nand!(atomic_nand_release__u64, u64);
            atomic_nand!(atomic_nand_release__usize, usize);
            atomic_nand!(atomic_nand_release__i128, i128);
            atomic_nand!(atomic_nand_release__u128, u128);

            // pub unsafe fn atomic_nand_acqrel<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            // {
            //     let result = *dst;
            //     *dst = abstract_value!(result);
            //     result
            // }
            atomic_nand!(atomic_nand_acqrel__i8, i8);
            atomic_nand!(atomic_nand_acqrel__i16, i16);
            atomic_nand!(atomic_nand_acqrel__i32, i32);
            atomic_nand!(atomic_nand_acqrel__i64, i64);
            atomic_nand!(atomic_nand_acqrel__isize, isize);
            atomic_nand!(atomic_nand_acqrel__u8, u8);
            atomic_nand!(atomic_nand_acqrel__u16, u16);
            atomic_nand!(atomic_nand_acqrel__u32, u32);
            atomic_nand!(atomic_nand_acqrel__u64, u64);
            atomic_nand!(atomic_nand_acqrel__usize, usize);
            atomic_nand!(atomic_nand_acqrel__i128, i128);
            atomic_nand!(atomic_nand_acqrel__u128, u128);

            // pub unsafe fn atomic_nand_relaxed<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            // {
            //     let result = *dst;
            //     *dst = abstract_value!(result);
            //     result
            // }
            atomic_nand!(atomic_nand_relaxed__i8, i8);
            atomic_nand!(atomic_nand_relaxed__i16, i16);
            atomic_nand!(atomic_nand_relaxed__i32, i32);
            atomic_nand!(atomic_nand_relaxed__i64, i64);
            atomic_nand!(atomic_nand_relaxed__isize, isize);
            atomic_nand!(atomic_nand_relaxed__u8, u8);
            atomic_nand!(atomic_nand_relaxed__u16, u16);
            atomic_nand!(atomic_nand_relaxed__u32, u32);
            atomic_nand!(atomic_nand_relaxed__u64, u64);
            atomic_nand!(atomic_nand_relaxed__usize, usize);
            atomic_nand!(atomic_nand_relaxed__i128, i128);
            atomic_nand!(atomic_nand_relaxed__u128, u128);

            // pub unsafe fn atomic_or_seqcst<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::BitOrAssign,
            // {
            //     let result = *dst;
            //     *dst |= src;
            //     result
            // }
            atomic_int!(atomic_or_seqcst__i8, i8, |=);
            atomic_int!(atomic_or_seqcst__i16, i16, |=);
            atomic_int!(atomic_or_seqcst__i32, i32, |=);
            atomic_int!(atomic_or_seqcst__i64, i64, |=);
            atomic_int!(atomic_or_seqcst__isize, isize, |=);
            atomic_int!(atomic_or_seqcst__u8, u8, |=);
            atomic_int!(atomic_or_seqcst__u16, u16, |=);
            atomic_int!(atomic_or_seqcst__u32, u32, |=);
            atomic_int!(atomic_or_seqcst__u64, u64, |=);
            atomic_int!(atomic_or_seqcst__usize, usize, |=);
            atomic_int!(atomic_or_seqcst__i128, i128, |=);
            atomic_int!(atomic_or_seqcst__u128, u128, |=);

            // pub unsafe fn atomic_or_acquire<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::BitOrAssign,
            // {
            //     let result = *dst;
            //     *dst |= src;
            //     result
            // }
            atomic_int!(atomic_or_acquire__i8, i8, |=);
            atomic_int!(atomic_or_acquire__i16, i16, |=);
            atomic_int!(atomic_or_acquire__i32, i32, |=);
            atomic_int!(atomic_or_acquire__i64, i64, |=);
            atomic_int!(atomic_or_acquire__isize, isize, |=);
            atomic_int!(atomic_or_acquire__u8, u8, |=);
            atomic_int!(atomic_or_acquire__u16, u16, |=);
            atomic_int!(atomic_or_acquire__u32, u32, |=);
            atomic_int!(atomic_or_acquire__u64, u64, |=);
            atomic_int!(atomic_or_acquire__usize, usize, |=);
            atomic_int!(atomic_or_acquire__i128, i128, |=);
            atomic_int!(atomic_or_acquire__u128, u128, |=);

            // pub unsafe fn atomic_or_release<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::BitOrAssign,
            // {
            //     let result = *dst;
            //     *dst |= src;
            //     result
            // }
            atomic_int!(atomic_or_release__i8, i8, |=);
            atomic_int!(atomic_or_release__i16, i16, |=);
            atomic_int!(atomic_or_release__i32, i32, |=);
            atomic_int!(atomic_or_release__i64, i64, |=);
            atomic_int!(atomic_or_release__isize, isize, |=);
            atomic_int!(atomic_or_release__u8, u8, |=);
            atomic_int!(atomic_or_release__u16, u16, |=);
            atomic_int!(atomic_or_release__u32, u32, |=);
            atomic_int!(atomic_or_release__u64, u64, |=);
            atomic_int!(atomic_or_release__usize, usize, |=);
            atomic_int!(atomic_or_release__i128, i128, |=);
            atomic_int!(atomic_or_release__u128, u128, |=);

            // pub unsafe fn atomic_or_acqrel<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::BitOrAssign,
            // {
            //     let result = *dst;
            //     *dst |= src;
            //     result
            // }
            atomic_int!(atomic_or_acqrel__i8, i8, |=);
            atomic_int!(atomic_or_acqrel__i16, i16, |=);
            atomic_int!(atomic_or_acqrel__i32, i32, |=);
            atomic_int!(atomic_or_acqrel__i64, i64, |=);
            atomic_int!(atomic_or_acqrel__isize, isize, |=);
            atomic_int!(atomic_or_acqrel__u8, u8, |=);
            atomic_int!(atomic_or_acqrel__u16, u16, |=);
            atomic_int!(atomic_or_acqrel__u32, u32, |=);
            atomic_int!(atomic_or_acqrel__u64, u64, |=);
            atomic_int!(atomic_or_acqrel__usize, usize, |=);
            atomic_int!(atomic_or_acqrel__i128, i128, |=);
            atomic_int!(atomic_or_acqrel__u128, u128, |=);

            // pub unsafe fn atomic_or_relaxed<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::BitOrAssign,
            // {
            //     let result = *dst;
            //     *dst |= src;
            //     result
            // }
            atomic_int!(atomic_or_relaxed__i8, i8, |=);
            atomic_int!(atomic_or_relaxed__i16, i16, |=);
            atomic_int!(atomic_or_relaxed__i32, i32, |=);
            atomic_int!(atomic_or_relaxed__i64, i64, |=);
            atomic_int!(atomic_or_relaxed__isize, isize, |=);
            atomic_int!(atomic_or_relaxed__u8, u8, |=);
            atomic_int!(atomic_or_relaxed__u16, u16, |=);
            atomic_int!(atomic_or_relaxed__u32, u32, |=);
            atomic_int!(atomic_or_relaxed__u64, u64, |=);
            atomic_int!(atomic_or_relaxed__usize, usize, |=);
            atomic_int!(atomic_or_relaxed__i128, i128, |=);
            atomic_int!(atomic_or_relaxed__u128, u128, |=);

            // pub unsafe fn atomic_xor_seqcst<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::BitXorAssign,
            // {
            //     let result = *dst;
            //     *dst ^= src;
            //     result
            // }
            atomic_int!(atomic_xor_seqcst__i8, i8, ^=);
            atomic_int!(atomic_xor_seqcst__i16, i16, ^=);
            atomic_int!(atomic_xor_seqcst__i32, i32, ^=);
            atomic_int!(atomic_xor_seqcst__i64, i64, ^=);
            atomic_int!(atomic_xor_seqcst__isize, isize, ^=);
            atomic_int!(atomic_xor_seqcst__u8, u8, ^=);
            atomic_int!(atomic_xor_seqcst__u16, u16, ^=);
            atomic_int!(atomic_xor_seqcst__u32, u32, ^=);
            atomic_int!(atomic_xor_seqcst__u64, u64, ^=);
            atomic_int!(atomic_xor_seqcst__usize, usize, ^=);
            atomic_int!(atomic_xor_seqcst__i128, i128, ^=);
            atomic_int!(atomic_xor_seqcst__u128, u128, ^=);

            // pub unsafe fn atomic_xor_acquire<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::BitXorAssign,
            // {
            //     let result = *dst;
            //     *dst ^= src;
            //     result
            // }
            atomic_int!(atomic_xor_acquire__i8, i8, ^=);
            atomic_int!(atomic_xor_acquire__i16, i16, ^=);
            atomic_int!(atomic_xor_acquire__i32, i32, ^=);
            atomic_int!(atomic_xor_acquire__i64, i64, ^=);
            atomic_int!(atomic_xor_acquire__isize, isize, ^=);
            atomic_int!(atomic_xor_acquire__u8, u8, ^=);
            atomic_int!(atomic_xor_acquire__u16, u16, ^=);
            atomic_int!(atomic_xor_acquire__u32, u32, ^=);
            atomic_int!(atomic_xor_acquire__u64, u64, ^=);
            atomic_int!(atomic_xor_acquire__usize, usize, ^=);
            atomic_int!(atomic_xor_acquire__i128, i128, ^=);
            atomic_int!(atomic_xor_acquire__u128, u128, ^=);

            // pub unsafe fn atomic_xor_release<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::BitXorAssign,
            // {
            //     let result = *dst;
            //     *dst ^= src;
            //     result
            // }
            atomic_int!(atomic_xor_release__i8, i8, ^=);
            atomic_int!(atomic_xor_release__i16, i16, ^=);
            atomic_int!(atomic_xor_release__i32, i32, ^=);
            atomic_int!(atomic_xor_release__i64, i64, ^=);
            atomic_int!(atomic_xor_release__isize, isize, ^=);
            atomic_int!(atomic_xor_release__u8, u8, ^=);
            atomic_int!(atomic_xor_release__u16, u16, ^=);
            atomic_int!(atomic_xor_release__u32, u32, ^=);
            atomic_int!(atomic_xor_release__u64, u64, ^=);
            atomic_int!(atomic_xor_release__usize, usize, ^=);
            atomic_int!(atomic_xor_release__i128, i128, ^=);
            atomic_int!(atomic_xor_release__u128, u128, ^=);

            // pub unsafe fn atomic_xor_acqrel<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::BitXorAssign,
            // {
            //     let result = *dst;
            //     *dst ^= src;
            //     result
            // }
            atomic_int!(atomic_xor_acqrel__i8, i8, ^=);
            atomic_int!(atomic_xor_acqrel__i16, i16, ^=);
            atomic_int!(atomic_xor_acqrel__i32, i32, ^=);
            atomic_int!(atomic_xor_acqrel__i64, i64, ^=);
            atomic_int!(atomic_xor_acqrel__isize, isize, ^=);
            atomic_int!(atomic_xor_acqrel__u8, u8, ^=);
            atomic_int!(atomic_xor_acqrel__u16, u16, ^=);
            atomic_int!(atomic_xor_acqrel__u32, u32, ^=);
            atomic_int!(atomic_xor_acqrel__u64, u64, ^=);
            atomic_int!(atomic_xor_acqrel__usize, usize, ^=);
            atomic_int!(atomic_xor_acqrel__i128, i128, ^=);
            atomic_int!(atomic_xor_acqrel__u128, u128, ^=);

            // pub unsafe fn atomic_xor_relaxed<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: std::ops::BitXorAssign,
            // {
            //     let result = *dst;
            //     *dst ^= src;
            //     result
            // }
            atomic_int!(atomic_xor_relaxed__i8, i8, ^=);
            atomic_int!(atomic_xor_relaxed__i16, i16, ^=);
            atomic_int!(atomic_xor_relaxed__i32, i32, ^=);
            atomic_int!(atomic_xor_relaxed__i64, i64, ^=);
            atomic_int!(atomic_xor_relaxed__isize, isize, ^=);
            atomic_int!(atomic_xor_relaxed__u8, u8, ^=);
            atomic_int!(atomic_xor_relaxed__u16, u16, ^=);
            atomic_int!(atomic_xor_relaxed__u32, u32, ^=);
            atomic_int!(atomic_xor_relaxed__u64, u64, ^=);
            atomic_int!(atomic_xor_relaxed__usize, usize, ^=);
            atomic_int!(atomic_xor_relaxed__i128, i128, ^=);
            atomic_int!(atomic_xor_relaxed__u128, u128, ^=);

            // pub unsafe fn atomic_max_seqcst<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: PartialOrd,
            // {
            //     if *dst <= src {
            //         src
            //     } else {
            //         *dst
            //     }
            // }
            atomic_max_min!(atomic_max_seqcst__i8, i8, <=);
            atomic_max_min!(atomic_max_seqcst__i16, i16, <=);
            atomic_max_min!(atomic_max_seqcst__i32, i32, <=);
            atomic_max_min!(atomic_max_seqcst__i64, i64, <=);
            atomic_max_min!(atomic_max_seqcst__isize, isize, <=);
            atomic_max_min!(atomic_umax_seqcst__u8, u8, <=);
            atomic_max_min!(atomic_umax_seqcst__u16, u16, <=);
            atomic_max_min!(atomic_umax_seqcst__u32, u32, <=);
            atomic_max_min!(atomic_umax_seqcst__u64, u64, <=);
            atomic_max_min!(atomic_umax_seqcst__usize, usize, <=);
            atomic_max_min!(atomic_max_seqcst__i128, i128, <=);
            atomic_max_min!(atomic_umax_seqcst__u128, u128, <=);

            // pub unsafe fn atomic_max_acquire<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: PartialOrd,
            // {
            //     if *dst <= src {
            //         src
            //     } else {
            //         *dst
            //     }
            // }
            atomic_max_min!(atomic_max_acquire__i8, i8, <=);
            atomic_max_min!(atomic_max_acquire__i16, i16, <=);
            atomic_max_min!(atomic_max_acquire__i32, i32, <=);
            atomic_max_min!(atomic_max_acquire__i64, i64, <=);
            atomic_max_min!(atomic_max_acquire__isize, isize, <=);
            atomic_max_min!(atomic_umax_acquire__u8, u8, <=);
            atomic_max_min!(atomic_umax_acquire__u16, u16, <=);
            atomic_max_min!(atomic_umax_acquire__u32, u32, <=);
            atomic_max_min!(atomic_umax_acquire__u64, u64, <=);
            atomic_max_min!(atomic_umax_acquire__usize, usize, <=);
            atomic_max_min!(atomic_max_acquire__i128, i128, <=);
            atomic_max_min!(atomic_umax_acquire__u128, u128, <=);

            // pub unsafe fn atomic_max_release<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: PartialOrd,
            // {
            //     if *dst <= src {
            //         src
            //     } else {
            //         *dst
            //     }
            // }
            atomic_max_min!(atomic_max_release__i8, i8, <=);
            atomic_max_min!(atomic_max_release__i16, i16, <=);
            atomic_max_min!(atomic_max_release__i32, i32, <=);
            atomic_max_min!(atomic_max_release__i64, i64, <=);
            atomic_max_min!(atomic_max_release__isize, isize, <=);
            atomic_max_min!(atomic_umax_release__u8, u8, <=);
            atomic_max_min!(atomic_umax_release__u16, u16, <=);
            atomic_max_min!(atomic_umax_release__u32, u32, <=);
            atomic_max_min!(atomic_umax_release__u64, u64, <=);
            atomic_max_min!(atomic_umax_release__usize, usize, <=);
            atomic_max_min!(atomic_max_release__i128, i128, <=);
            atomic_max_min!(atomic_umax_release__u128, u128, <=);

            // pub unsafe fn atomic_max_acqrel<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: PartialOrd,
            // {
            //     if *dst <= src {
            //         src
            //     } else {
            //         *dst
            //     }
            // }
            atomic_max_min!(atomic_max_acqrel__i8, i8, <=);
            atomic_max_min!(atomic_max_acqrel__i16, i16, <=);
            atomic_max_min!(atomic_max_acqrel__i32, i32, <=);
            atomic_max_min!(atomic_max_acqrel__i64, i64, <=);
            atomic_max_min!(atomic_max_acqrel__isize, isize, <=);
            atomic_max_min!(atomic_umax_acqrel__u8, u8, <=);
            atomic_max_min!(atomic_umax_acqrel__u16, u16, <=);
            atomic_max_min!(atomic_umax_acqrel__u32, u32, <=);
            atomic_max_min!(atomic_umax_acqrel__u64, u64, <=);
            atomic_max_min!(atomic_umax_acqrel__usize, usize, <=);
            atomic_max_min!(atomic_max_acqrel__i128, i128, <=);
            atomic_max_min!(atomic_umax_acqrel__u128, u128, <=);

            // pub unsafe fn atomic_max_relaxed<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: PartialOrd,
            // {
            //     if *dst <= src {
            //         src
            //     } else {
            //         *dst
            //     }
            // }
            atomic_max_min!(atomic_max_relaxed__i8, i8, <=);
            atomic_max_min!(atomic_max_relaxed__i16, i16, <=);
            atomic_max_min!(atomic_max_relaxed__i32, i32, <=);
            atomic_max_min!(atomic_max_relaxed__i64, i64, <=);
            atomic_max_min!(atomic_max_relaxed__isize, isize, <=);
            atomic_max_min!(atomic_umax_relaxed__u8, u8, <=);
            atomic_max_min!(atomic_umax_relaxed__u16, u16, <=);
            atomic_max_min!(atomic_umax_relaxed__u32, u32, <=);
            atomic_max_min!(atomic_umax_relaxed__u64, u64, <=);
            atomic_max_min!(atomic_umax_relaxed__usize, usize, <=);
            atomic_max_min!(atomic_max_relaxed__i128, i128, <=);
            atomic_max_min!(atomic_umax_relaxed__u128, u128, <=);

            // pub unsafe fn atomic_min_seqcst<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: PartialOrd,
            // {
            //     if *dst >= src {
            //         src
            //     } else {
            //         *dst
            //     }
            // }
            atomic_max_min!(atomic_min_seqcst__i8, i8, >=);
            atomic_max_min!(atomic_min_seqcst__i16, i16, >=);
            atomic_max_min!(atomic_min_seqcst__i32, i32, >=);
            atomic_max_min!(atomic_min_seqcst__i64, i64, >=);
            atomic_max_min!(atomic_min_seqcst__isize, isize, >=);
            atomic_max_min!(atomic_umin_seqcst__u8, u8, >=);
            atomic_max_min!(atomic_umin_seqcst__u16, u16, >=);
            atomic_max_min!(atomic_umin_seqcst__u32, u32, >=);
            atomic_max_min!(atomic_umin_seqcst__u64, u64, >=);
            atomic_max_min!(atomic_umin_seqcst__usize, usize, >=);
            atomic_max_min!(atomic_min_seqcst__i128, i128, >=);
            atomic_max_min!(atomic_umin_seqcst__u128, u128, >=);

            // pub unsafe fn atomic_min_acquire<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: PartialOrd,
            // {
            //     if *dst >= src {
            //         src
            //     } else {
            //         *dst
            //     }
            // }
            atomic_max_min!(atomic_min_acquire__i8, i8, >=);
            atomic_max_min!(atomic_min_acquire__i16, i16, >=);
            atomic_max_min!(atomic_min_acquire__i32, i32, >=);
            atomic_max_min!(atomic_min_acquire__i64, i64, >=);
            atomic_max_min!(atomic_min_acquire__isize, isize, >=);
            atomic_max_min!(atomic_umin_acquire__u8, u8, >=);
            atomic_max_min!(atomic_umin_acquire__u16, u16, >=);
            atomic_max_min!(atomic_umin_acquire__u32, u32, >=);
            atomic_max_min!(atomic_umin_acquire__u64, u64, >=);
            atomic_max_min!(atomic_umin_acquire__usize, usize, >=);
            atomic_max_min!(atomic_min_acquire__i128, i128, >=);
            atomic_max_min!(atomic_umin_acquire__u128, u128, >=);

            // pub unsafe fn atomic_min_release<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: PartialOrd,
            // {
            //     if *dst >= src {
            //         src
            //     } else {
            //         *dst
            //     }
            // }
            atomic_max_min!(atomic_min_release__i8, i8, >=);
            atomic_max_min!(atomic_min_release__i16, i16, >=);
            atomic_max_min!(atomic_min_release__i32, i32, >=);
            atomic_max_min!(atomic_min_release__i64, i64, >=);
            atomic_max_min!(atomic_min_release__isize, isize, >=);
            atomic_max_min!(atomic_umin_release__u8, u8, >=);
            atomic_max_min!(atomic_umin_release__u16, u16, >=);
            atomic_max_min!(atomic_umin_release__u32, u32, >=);
            atomic_max_min!(atomic_umin_release__u64, u64, >=);
            atomic_max_min!(atomic_umin_release__usize, usize, >=);
            atomic_max_min!(atomic_min_release__i128, i128, >=);
            atomic_max_min!(atomic_umin_release__u128, u128, >=);

            // pub unsafe fn atomic_min_acqrel<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: PartialOrd,
            // {
            //     if *dst >= src {
            //         src
            //     } else {
            //         *dst
            //     }
            // }
            atomic_max_min!(atomic_min_acqrel__i8, i8, >=);
            atomic_max_min!(atomic_min_acqrel__i16, i16, >=);
            atomic_max_min!(atomic_min_acqrel__i32, i32, >=);
            atomic_max_min!(atomic_min_acqrel__i64, i64, >=);
            atomic_max_min!(atomic_min_acqrel__isize, isize, >=);
            atomic_max_min!(atomic_umin_acqrel__u8, u8, >=);
            atomic_max_min!(atomic_umin_acqrel__u16, u16, >=);
            atomic_max_min!(atomic_umin_acqrel__u32, u32, >=);
            atomic_max_min!(atomic_umin_acqrel__u64, u64, >=);
            atomic_max_min!(atomic_umin_acqrel__usize, usize, >=);
            atomic_max_min!(atomic_min_acqrel__i128, i128, >=);
            atomic_max_min!(atomic_umin_acqrel__u128, u128, >=);

            // pub unsafe fn atomic_min_relaxed<T>(dst: *mut T, src: T) -> T
            // where
            //     T: Copy,
            //     T: PartialOrd,
            // {
            //     if *dst >= src {
            //         src
            //     } else {
            //         *dst
            //     }
            // }
            atomic_max_min!(atomic_min_relaxed__i8, i8, >=);
            atomic_max_min!(atomic_min_relaxed__i16, i16, >=);
            atomic_max_min!(atomic_min_relaxed__i32, i32, >=);
            atomic_max_min!(atomic_min_relaxed__i64, i64, >=);
            atomic_max_min!(atomic_min_relaxed__isize, isize, >=);
            atomic_max_min!(atomic_umin_relaxed__u8, u8, >=);
            atomic_max_min!(atomic_umin_relaxed__u16, u16, >=);
            atomic_max_min!(atomic_umin_relaxed__u32, u32, >=);
            atomic_max_min!(atomic_umin_relaxed__u64, u64, >=);
            atomic_max_min!(atomic_umin_relaxed__usize, usize, >=);
            atomic_max_min!(atomic_min_relaxed__i128, i128, >=);
            atomic_max_min!(atomic_umin_relaxed__u128, u128, >=);

            default_contract!(atomic_fence_seqcst);
            default_contract!(atomic_fence_acquire);
            default_contract!(atomic_fence_release);
            default_contract!(atomic_fence_acqrel);
            default_contract!(atomic_singlethreadfence_seqcst);
            default_contract!(atomic_singlethreadfence_acquire);
            default_contract!(atomic_singlethreadfence_release);
            default_contract!(atomic_singlethreadfence_acqrel);

            default_contract!(prefetch_read_data);
            default_contract!(prefetch_write_data);
            default_contract!(prefetch_read_instruction);
            default_contract!(prefetch_write_instruction);
            default_contract!(is_aligned_and_not_null);
            default_contract!(is_nonoverlapping);

            default_contract!(assert_inhabited);
            default_contract!(assert_zero_valid);
            default_contract!(assert_uninit_valid);
            default_contract!(rustc_peek);
            pub fn abort() {
                assume_unreachable!();
            }
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
            default_contract!(breakpoint);
            pub unsafe fn move_val_init<T>(dst: *mut T, src: T)
            where
                T: Copy,
            {
                *dst = src;
            }
            pub fn min_align_of<T>() -> usize {
                4
            }
            // pub fn pref_align_of<T>() -> usize {
            //     result!()
            // }
            //todo: implement these inside MIRAI
            pub fn type_name<T: ?Sized>() -> &'static str {
                result!()
            }
            pub fn type_id<T: ?Sized + 'static>() -> u64 {
                result!()
            }
            pub fn panic_if_uninhabited<T>() {
                // Compiler bootstrapping support. Nothing to do here when analyzing.
            }
            default_contract!(caller_location);
            default_contract!(init);
            default_contract!(uninit);
            pub fn forget<T>(_: T) {}
            pub unsafe fn volatile_copy_nonoverlapping_memory<T>(
                dst: *mut T,
                src: *const T,
                count: usize,
            ) {
                std::intrinsics::copy_nonoverlapping(src, dst, count);
            }
            // pub fn volatile_copy_memory<T>(dst: *mut T, src: *const T, count: usize) {}
            // pub fn volatile_set_memory<T>(dst: *mut T, val: T, count: usize) {
            //     *dst = val;
            // }
            // pub fn volatile_load<T>(src: *const T) -> T {
            //     *src
            // }
            // pub fn volatile_store<T>(dst: *mut T, val: T) {
            //     *dst = val;
            // }
            // pub fn unaligned_volatile_load<T>(src: *const T) -> T {
            //     *src
            // }
            // pub fn unaligned_volatile_store<T>(dst: *mut T, val: T) {
            //     *dst = val
            // }

            default_contract!(float_to_int_unchecked);
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
            add_with_overflow!(u8, u128, add_with_overflow__u8, std::u8::MAX);
            add_with_overflow!(u16, u128, add_with_overflow__u16, std::u16::MAX);
            add_with_overflow!(u32, u128, add_with_overflow__u32, std::u32::MAX);
            add_with_overflow!(u64, u128, add_with_overflow__u64, std::u64::MAX);
            add_with_overflow!(usize, u128, add_with_overflow__usize, std::usize::MAX);
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
            exact_signed_div!(i8, exact_div__i8, i8::MIN);
            exact_signed_div!(i16, exact_div__i16, i16::MIN);
            exact_signed_div!(i32, exact_div__i32, i32::MIN);
            exact_signed_div!(i64, exact_div__i64, i64::MIN);
            exact_signed_div!(i128, exact_div__i128, i128::MIN);
            exact_signed_div!(isize, exact_div__isize, isize::MIN);
            exact_div!(u8, exact_div__u8);
            exact_div!(u16, exact_div__u16);
            exact_div!(u32, exact_div__u32);
            exact_div!(u64, exact_div__u64);
            exact_div!(u128, exact_div__u128);
            exact_div!(usize, exact_div__usize);

            unchecked_signed_div!(i8, unchecked_div__i8, i8::MIN);
            unchecked_signed_div!(i16, unchecked_div__i16, i16::MIN);
            unchecked_signed_div!(i32, unchecked_div__i32, i32::MIN);
            unchecked_signed_div!(i64, unchecked_div__i64, i64::MIN);
            unchecked_signed_div!(i128, unchecked_div__i128, i128::MIN);
            unchecked_signed_div!(isize, unchecked_div__isize, isize::MIN);
            unchecked_div!(u8, unchecked_div__u8);
            unchecked_div!(u16, unchecked_div__u16);
            unchecked_div!(u32, unchecked_div__u32);
            unchecked_div!(u64, unchecked_div__u64);
            unchecked_div!(u128, unchecked_div__u128);
            unchecked_div!(usize, unchecked_div__usize);

            unchecked_signed_rem!(i8, unchecked_rem__i8, i8::MIN);
            unchecked_signed_rem!(i16, unchecked_rem__i16, i16::MIN);
            unchecked_signed_rem!(i32, unchecked_rem__i32, i32::MIN);
            unchecked_signed_rem!(i64, unchecked_rem__i64, i64::MIN);
            unchecked_signed_rem!(i128, unchecked_rem__i128, i128::MIN);
            unchecked_signed_rem!(isize, unchecked_rem__isize, isize::MIN);
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

            unchecked_add!(i8, i128, unchecked_add__i8, i8::MAX);
            unchecked_add!(i16, i128, unchecked_add__i16, i16::MAX);
            unchecked_add!(i32, i128, unchecked_add__i32, i32::MAX);
            unchecked_add!(i64, i128, unchecked_add__i64, i64::MAX);
            unchecked_add!(i128, i128, unchecked_add__i128, i128::MAX);
            unchecked_add!(isize, i128, unchecked_add__isize, i128::MAX);
            unchecked_add!(u8, u128, unchecked_add__u8, u8::MAX);
            unchecked_add!(u16, u128, unchecked_add__u16, u16::MAX);
            unchecked_add!(u32, u128, unchecked_add__u32, u32::MAX);
            unchecked_add!(u64, u128, unchecked_add__u64, u64::MAX);
            unchecked_add!(u128, u128, unchecked_add__u128, u128::MAX);
            unchecked_add!(usize, u128, unchecked_add__usize, usize::MAX);

            unchecked_sub!(i8, unchecked_sub__i8, i8::MAX);
            unchecked_sub!(i16, unchecked_sub__i16, i16::MAX);
            unchecked_sub!(i32, unchecked_sub__i32, i32::MAX);
            unchecked_sub!(i64, unchecked_sub__i64, i64::MAX);
            unchecked_sub!(isize, unchecked_sub__isize, i128::MAX);
            unchecked_sub!(u8, unchecked_sub__u8, u8::MAX);
            unchecked_sub!(u16, unchecked_sub__u16, u16::MAX);
            unchecked_sub!(u32, unchecked_sub__u32, u32::MAX);
            unchecked_sub!(u64, unchecked_sub__u64, u64::MAX);
            pub fn unchecked_sub__usize(x: usize, y: usize) -> usize {
                // Do not enable these preconditions until the prover can handle ptr1 - ptr2
                // where ptr1 has been widened.
                // precondition!((x as i128) - (y as i128) >= 0);
                // precondition!((x as i128) - (y as i128) <= (usize::MAX as i128));
                x - y
            }

            unchecked_mul!(i8, i128, unchecked_mul__i8, i8::MAX);
            unchecked_mul!(i16, i128, unchecked_mul__i16, i16::MAX);
            unchecked_mul!(i32, i128, unchecked_mul__i32, i32::MAX);
            unchecked_mul!(i64, i128, unchecked_mul__i64, i64::MAX);
            unchecked_mul!(i128, i128, unchecked_mul__i128, i128::MAX);
            unchecked_mul!(isize, i128, unchecked_mul__isize, isize::MAX);
            unchecked_mul!(u8, u128, unchecked_mul__u8, u8::MAX);
            unchecked_mul!(u16, u128, unchecked_mul__u16, u16::MAX);
            unchecked_mul!(u32, u128, unchecked_mul__u32, u32::MAX);
            unchecked_mul!(u64, u128, unchecked_mul__u64, u64::MAX);
            unchecked_mul!(u128, u128, unchecked_mul__u128, u128::MAX);
            unchecked_mul!(usize, u128, unchecked_mul__usize, usize::MAX);

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
            wrapping_add!(i8, i128, wrapping_add__i8, i8::MAX);
            wrapping_add!(i16, i128, wrapping_add__i16, i16::MAX);
            wrapping_add!(i32, i128, wrapping_add__i32, i32::MAX);
            wrapping_add!(i64, i128, wrapping_add__i64, i64::MAX);
            wrapping_add!(isize, i128, wrapping_add__isize, isize::MAX);
            wrapping_add!(u8, u128, wrapping_add__u8, u8::MAX);
            wrapping_add!(u16, u128, wrapping_add__u16, u16::MAX);
            wrapping_add!(u32, u128, wrapping_add__u32, u32::MAX);
            wrapping_add!(u64, u128, wrapping_add__u64, u64::MAX);
            wrapping_add!(usize, u128, wrapping_add__usize, usize::MAX);
            default_contract!(wrapping_add__i128);
            default_contract!(wrapping_add__u128);

            // (a - b) mod 2 ** N, where N is the width of T in bits.
            wrapping_sub!(i8, i128, wrapping_sub__i8, i8::MAX);
            wrapping_sub!(i16, i128, wrapping_sub__i16, i16::MAX);
            wrapping_sub!(i32, i128, wrapping_sub__i32, i32::MAX);
            wrapping_sub!(i64, i128, wrapping_sub__i64, i64::MAX);
            wrapping_sub!(isize, i128, wrapping_sub__isize, isize::MAX);
            wrapping_sub!(u8, i128, wrapping_sub__u8, u8::MAX);
            wrapping_sub!(u16, i128, wrapping_sub__u16, u16::MAX);
            wrapping_sub!(u32, i128, wrapping_sub__u32, u32::MAX);
            wrapping_sub!(u64, i128, wrapping_sub__u64, u64::MAX);
            wrapping_sub!(usize, i128, wrapping_sub__usize, usize::MAX);
            default_contract!(wrapping_sub__i128);
            default_contract!(wrapping_sub__u128);

            // (a * b) mod 2 ** N, where N is the width of T in bits.
            wrapping_mul!(i8, i128, wrapping_mul__i8, i8::MAX);
            wrapping_mul!(i16, i128, wrapping_mul__i16, i16::MAX);
            wrapping_mul!(i32, i128, wrapping_mul__i32, i32::MAX);
            wrapping_mul!(i64, i128, wrapping_mul__i64, i64::MAX);
            wrapping_mul!(isize, i128, wrapping_mul__isize, isize::MAX);
            wrapping_mul!(u8, u128, wrapping_mul__u8, u8::MAX);
            wrapping_mul!(u16, u128, wrapping_mul__u16, u16::MAX);
            wrapping_mul!(u32, u128, wrapping_mul__u32, u32::MAX);
            wrapping_mul!(u64, u128, wrapping_mul__u64, u64::MAX);
            wrapping_mul!(usize, u128, wrapping_mul__usize, usize::MAX);
            default_contract!(wrapping_mul__i128);
            default_contract!(wrapping_mul__u128);

            saturating_add!(i8, i128, saturating_add__i8, i8::MAX);
            saturating_add!(i16, i128, saturating_add__i16, i16::MAX);
            saturating_add!(i32, i128, saturating_add__i32, i32::MAX);
            saturating_add!(i64, i128, saturating_add__i64, i64::MAX);
            saturating_add!(isize, i128, saturating_add__isize, isize::MAX);
            saturating_add!(u8, u128, saturating_add__u8, u8::MAX);
            saturating_add!(u16, u128, saturating_add__u16, u16::MAX);
            saturating_add!(u32, u128, saturating_add__u32, u32::MAX);
            saturating_add!(u64, u128, saturating_add__u64, u64::MAX);
            saturating_add!(usize, u128, saturating_add__usize, usize::MAX);
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
            default_contract!(r#try);
            // pub fn nontemporal_store<T>(ptr: *mut T, val: T) {
            //     *ptr = val;
            // }
            pub fn ptr_offset_from<T>(ptr: *const T, base: *const T) -> isize {
                // todo: implement this inside MIRAI
                result!()
            }
            pub fn miri_start_panic<T>(data: T) {
                assume_unreachable!()
            }
            default_contract!(count_code_region);
            pub fn ptr_guaranteed_eq<T>(ptr: *const T, other: *const T) -> bool {
                ptr == other
            }
            pub fn ptr_guaranteed_ne<T>(ptr: *const T, other: *const T) -> bool {
                ptr != other
            }
            pub fn ptr_guaranteed_cmp(a: *const (), b: *const ()) -> u8 {
                match (ptr_guaranteed_eq(a, b), ptr_guaranteed_ne(a, b)) {
                    (false, false) => 2,
                    (true, false) => 1,
                    (false, true) => 0,
                    (true, true) => unreachable!(),
                }
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
            pub fn into__ref_str_alloc_boxed_Box_trait_std_error_Error_alloc_alloc_Global(
                s: &str,
            ) -> Box<&str> {
                Box::new(s)
            }
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
            pub mod map {
                pub mod implement_core_iter_adapters_map_Map_generic_par_I_generic_par_F {
                    fn MAY_HAVE_SIDE_EFFECT() -> bool {
                        true
                    }
                }
            }
            pub mod map_fold {
                default_contract!(closure);
            }
            pub mod zip {
                pub mod implement_core_iter_adapters_zip_Zip_generic_par_A_generic_par_B {
                    fn MAY_HAVE_SIDE_EFFECT() -> bool {
                        true
                    }
                }
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
                panic!("result unwrap failed")
            }
        }

        pub mod traits {
            pub mod accum {
                pub mod Sum {
                    default_contract!(sum);
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
        pub mod implement_core_mem_Discriminant_generic_par_T {
            pub struct Discriminant(u128);

            fn eq<T>(_self: &Discriminant, rhs: &Discriminant) -> bool {
                (_self.0 as u128) == (rhs.0 as u128)
            }
        }
    }

    pub mod num {
        fn ASCII_CASE_MASK() -> u8 {
            0b0010_0000
        }

        pub mod implement_isize {
            default_contract!(from_str);
            default_contract!(from_str_radix);

            pub fn MAX() -> isize {
                if cfg!(any(
                    target_arch = "x86",
                    target_arch = "mips",
                    target_arch = "powerpc",
                    target_arch = "arm"
                )) {
                    2147483647
                } else if cfg!(any(
                    target_arch = "x86_64",
                    target_arch = "powerpc64",
                    target_arch = "aarch64"
                )) {
                    9223372036854775807
                } else {
                    panic!("Unsupported architecture");
                }
            }
            pub fn max_value() -> isize {
                if cfg!(any(
                    target_arch = "x86",
                    target_arch = "mips",
                    target_arch = "powerpc",
                    target_arch = "arm"
                )) {
                    2147483647
                } else if cfg!(any(
                    target_arch = "x86_64",
                    target_arch = "powerpc64",
                    target_arch = "aarch64"
                )) {
                    9223372036854775807
                } else {
                    panic!("Unsupported architecture");
                }
            }
            pub fn MIN() -> isize {
                if cfg!(any(
                    target_arch = "x86",
                    target_arch = "mips",
                    target_arch = "powerpc",
                    target_arch = "arm"
                )) {
                    -2147483648
                } else if cfg!(any(
                    target_arch = "x86_64",
                    target_arch = "powerpc64",
                    target_arch = "aarch64"
                )) {
                    -9223372036854775808
                } else {
                    panic!("Unsupported architecture");
                }
            }
            pub fn min_value() -> isize {
                if cfg!(any(
                    target_arch = "x86",
                    target_arch = "mips",
                    target_arch = "powerpc",
                    target_arch = "arm"
                )) {
                    -2147483648
                } else if cfg!(any(
                    target_arch = "x86_64",
                    target_arch = "powerpc64",
                    target_arch = "aarch64"
                )) {
                    -9223372036854775808
                } else {
                    panic!("Unsupported architecture");
                }
            }
        }

        pub mod implement_i8 {
            default_contract!(from_str);
            default_contract!(from_str_radix);

            pub fn MAX() -> i8 {
                127
            }
            pub fn max_value() -> i8 {
                127
            }
            pub fn MIN() -> i8 {
                -128
            }
            pub fn min_value() -> i8 {
                -128
            }
        }

        pub mod implement_i16 {
            default_contract!(from_str);
            default_contract!(from_str_radix);

            pub fn MAX() -> i16 {
                32767
            }
            pub fn max_value() -> i16 {
                32767
            }
            pub fn MIN() -> i16 {
                -32768
            }
            pub fn min_value() -> i16 {
                -32768
            }
        }

        pub mod implement_i32 {
            default_contract!(from_str);
            default_contract!(from_str_radix);

            pub fn MAX() -> i32 {
                2147483647
            }
            pub fn max_value() -> i32 {
                2147483647
            }
            pub fn MIN() -> i32 {
                -2147483648
            }
            pub fn min_value() -> i32 {
                -2147483648
            }
        }

        pub mod implement_i64 {
            default_contract!(from_str);
            default_contract!(from_str_radix);

            pub fn MAX() -> i64 {
                9223372036854775807
            }
            pub fn max_value() -> i64 {
                9223372036854775807
            }
            pub fn MIN() -> i64 {
                -9223372036854775808
            }
            pub fn min_value() -> i64 {
                -9223372036854775808
            }
        }

        pub mod implement_i128 {
            default_contract!(from_str);
            default_contract!(from_str_radix);

            pub fn MAX() -> i128 {
                170141183460469231731687303715884105727
            }
            pub fn max_value() -> i128 {
                170141183460469231731687303715884105727
            }
            pub fn MIN() -> i128 {
                -170141183460469231731687303715884105728
            }
            pub fn min_value() -> i128 {
                -170141183460469231731687303715884105728
            }
        }

        pub mod implement_usize {
            pub fn checked_add(_self: usize, value: usize) -> Option<usize> {
                if _self > max_value() - value {
                    None
                } else {
                    Some(_self + value)
                }
            }

            default_contract!(from_str);
            default_contract!(from_str_radix);

            pub fn is_power_of_two(n: usize) -> bool {
                if cfg!(any(
                    target_arch = "x86",
                    target_arch = "mips",
                    target_arch = "powerpc",
                    target_arch = "arm"
                )) {
                    (n as u32).is_power_of_two()
                } else if cfg!(any(
                    target_arch = "x86_64",
                    target_arch = "powerpc64",
                    target_arch = "aarch64"
                )) {
                    (n as u64).is_power_of_two()
                } else {
                    panic!("Unsupported architecture");
                }
            }

            pub fn MAX() -> usize {
                if cfg!(any(
                    target_arch = "x86",
                    target_arch = "mips",
                    target_arch = "powerpc",
                    target_arch = "arm"
                )) {
                    4294967295
                } else if cfg!(any(
                    target_arch = "x86_64",
                    target_arch = "powerpc64",
                    target_arch = "aarch64"
                )) {
                    18446744073709551615
                } else {
                    panic!("Unsupported architecture");
                }
            }
            pub fn max_value() -> usize {
                if cfg!(any(
                    target_arch = "x86",
                    target_arch = "mips",
                    target_arch = "powerpc",
                    target_arch = "arm"
                )) {
                    4294967295
                } else if cfg!(any(
                    target_arch = "x86_64",
                    target_arch = "powerpc64",
                    target_arch = "aarch64",
                )) {
                    18446744073709551615
                } else {
                    panic!("Unsupported architecture");
                }
            }
            pub fn MIN() -> usize {
                0
            }
            pub fn min_value() -> usize {
                0
            }
        }

        pub mod implement_u8 {
            default_contract!(from_str);
            default_contract!(from_str_radix);

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

            pub fn MAX() -> u8 {
                255
            }
            pub fn MIN() -> u8 {
                0
            }
        }

        pub mod implement_u16 {
            default_contract!(from_str);
            default_contract!(from_str_radix);

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

            pub fn MAX() -> u16 {
                65535
            }
            pub fn max_value() -> u16 {
                65535
            }
            pub fn MIN() -> u16 {
                0
            }
            pub fn min_value() -> u16 {
                0
            }
        }

        pub mod implement_u32 {
            default_contract!(from_str);
            default_contract!(from_str_radix);

            pub fn MAX() -> u32 {
                4294967295
            }
            pub fn max_value() -> u32 {
                4294967295
            }
            pub fn MIN() -> u32 {
                0
            }
            pub fn min_value() -> u32 {
                0
            }
        }

        pub mod implement_u64 {
            default_contract!(from_str);
            default_contract!(from_str_radix);

            pub fn MAX() -> u64 {
                18446744073709551615
            }
            pub fn max_value() -> u64 {
                18446744073709551615
            }
            pub fn MIN() -> u64 {
                0
            }
            pub fn min_value() -> u64 {
                0
            }
        }

        pub mod implement_u128 {
            default_contract!(from_str);
            default_contract!(from_str_radix);

            pub fn MAX() -> u128 {
                340282366920938463463374607431768211455
            }
            pub fn max_value() -> u128 {
                340282366920938463463374607431768211455
            }
            pub fn MIN() -> u128 {
                0
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

        pub mod control_flow {
            pub mod implement_core_ops_control_flow_ControlFlow_generic_par_B_tuple_0 {
                pub fn BREAK() -> core::ops::ControlFlow<()> {
                    core::ops::ControlFlow::Break(())
                }
                pub fn CONTINUE() -> core::ops::ControlFlow<()> {
                    core::ops::ControlFlow::Continue(())
                }
            }
            pub mod implement_core_ops_control_flow_ControlFlow_tuple_0_generic_par_C {
                pub fn BREAK() -> core::ops::ControlFlow<()> {
                    core::ops::ControlFlow::Break(())
                }
                pub fn CONTINUE() -> core::ops::ControlFlow<()> {
                    core::ops::ControlFlow::Continue(())
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
        pub mod implement {
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
            panic!("result unwrap failed")
        }
    }

    pub mod slice {
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

        pub mod iter {
            pub mod implement_core_slice_iter_Iter_generic_par_T {
                pub fn MAY_HAVE_SIDE_EFFECT() -> bool {
                    false
                }
            }
            pub mod implement_core_slice_iter_IterMut_generic_par_T {
                pub fn MAY_HAVE_SIDE_EFFECT() -> bool {
                    false
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
            default_contract!(memrchr);
        }
    }

    pub mod str {
        pub mod converts {
            default_contract!(from_utf8);
        }

        pub mod implement {
            default_contract!(parse);
            default_contract!(trim);
        }

        pub mod implement_ref_str {
            pub fn default() -> &'static str {
                ""
            }
        }

        pub mod pattern {
            pub mod implement_core_str_pattern_StrSearcher {
                use core::str::pattern::StrSearcher;

                default_contract!(new);

                default_contract!(next_match);
            }

            pub mod implement_core_str_pattern_TwoWaySearcher {
                default_contract!(next);
            }

            pub mod Searcher {
                default_contract!(next_reject);
            }
        }

        pub fn slice_error_fail(s: &str, begin: usize, end: usize) -> ! {
            panic!("byte index is not a char boundary");
        }

        pub mod validations {
            pub fn CONT_MASK() -> u8 {
                0b0011_1111
            }
            pub fn TAG_CONT_U8() -> u8 {
                0b1000_0000
            }
        }
    }

    pub mod task {
        pub mod wake {
            pub mod implement_core_task_wake_Waker {
                default_contract!(wake);
            }
        }
    }

    pub mod time {
        pub fn NANOS_PER_SEC() -> u32 {
            1_000_000_000
        }
        pub fn NANOS_PER_MILLI() -> u32 {
            1_000_000
        }
        pub fn NANOS_PER_MICRO() -> u32 {
            1_000
        }
        pub fn MILLIS_PER_SEC() -> u64 {
            1_000
        }
        pub fn MICROS_PER_SEC() -> u64 {
            1_000_000
        }

        pub mod implement_core_time_Duration {
            default_contract!(mul);
        }
    }

    pub mod unicode {
        pub mod unicode_data {
            pub mod alphabetic {
                default_contract!(lookup);
            }
            pub mod case_ignorable {
                default_contract!(lookup);
            }
            pub mod cased {
                default_contract!(lookup);
            }
            pub mod cc {
                default_contract!(lookup);
            }
            pub mod grapheme_extend {
                default_contract!(lookup);
            }
            pub mod lowercase {
                default_contract!(lookup);
            }
            pub mod n {
                default_contract!(lookup);
            }
            pub mod uppercase {
                default_contract!(lookup);
            }
            pub mod white_space {
                default_contract!(lookup);
            }
            pub mod conversions {
                default_contract!(to_lower);
                default_contract!(to_upper);
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

pub mod diem_logger {
    pub mod logger {
        pub mod Logger {
            default_contract!(enabled);
            default_contract!(record);
        }
    }
}

pub mod hashbrown {
    pub mod raw {
        fn DELETED() -> u8 {
            0b1000_0000
        }
        fn EMPTY() -> u8 {
            0b1111_1111
        }

        pub mod implement {
            default_contract!(alloc_err);
            default_contract!(capacity_overflow);
        }
        pub mod implement_hashbrown_raw_RawTable_generic_par_T {
            default_contract!(rehash_in_place);
            default_contract!(resize);
        }

        pub mod inner {
            pub mod sse2 {
                pub mod implement {
                    fn WIDTH() -> usize {
                        16
                    }
                }
                fn BITMASK_MASK() -> u16 {
                    0xffff
                }
                fn BITMASK_STRIDE() -> usize {
                    1
                }
            }
        }

        pub mod sse2 {
            fn BITMASK_MASK() -> u16 {
                0xffff
            }
            fn BITMASK_STRIDE() -> usize {
                1
            }
            pub mod implement {
                default_contract!(static_empty);
                #[cfg(any(
                    target_arch = "x86",
                    target_arch = "mips",
                    target_arch = "mips",
                    target_arch = "powerpc",
                    target_arch = "arm"
                ))]
                fn WIDTH() -> usize {
                    4
                }
                #[cfg(any(
                    target_arch = "x86_64",
                    target_arch = "powerpc64",
                    target_arch = "aarch64"
                ))]
                fn WIDTH() -> usize {
                    8
                }
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
        pub mod foreign {
            pub fn dlsym() -> u64 {
                0
            }

            pub fn open() -> u64 {
                0
            }

            pub fn pthread_cond_destroy() -> u64 {
                0
            }

            pub fn pthread_cond_timedwait() -> u64 {
                0
            }

            pub fn pthread_cond_wait() -> u64 {
                0
            }

            pub fn pthread_mutex_destroy() -> u64 {
                0
            }

            pub fn pthread_mutex_lock() -> u64 {
                0
            }

            pub fn pthread_rwlock_unlock() -> u64 {
                0
            }

            pub fn pthread_rwlock_rdlock() -> u64 {
                0
            }

            pub fn pthread_cond_signal() -> u64 {
                0
            }

            pub fn pthread_mutex_unlock() -> u64 {
                0
            }

            pub fn pthread_rwlock_wrlock() -> u64 {
                0
            }

            pub fn read() -> u64 {
                0
            }

            default_contract!(tcgetattr);
            default_contract!(tcsetattr);
            default_contract!(sysconf);
        }

        pub mod bsd {
            pub mod apple {
                pub fn __error() -> &'static i32 {
                    &-1
                }
                default_contract!(gettimeofday);
            }

            default_contract!(ioctl);
        }
    }
}

pub mod log {
    default_contract!(__private_api_log);
}

pub mod measureme {
    pub mod profiler {
        pub mod implement {
            default_contract!(nanos_since_start);
            default_contract!(record_raw_event);
        }
    }
}

pub mod move_binary_format {
    pub mod file_format {
        pub enum IndexKind {
            ModuleHandle,
            StructHandle,
            FunctionHandle,
            FieldHandle,
            FriendDeclaration,
            FunctionInstantiation,
            FieldInstantiation,
            StructDefinition,
            StructDefInstantiation,
            FunctionDefinition,
            FieldDefinition,
            Signature,
            Identifier,
            AddressIdentifier,
            ConstantPool,
            LocalPool,
            CodeDefinition,
            TypeParameter,
            MemberCount,
        }

        pub mod implement_move_binary_format_file_format_AddressIdentifierIndex {
            use crate::foreign_contracts::move_binary_format::file_format::IndexKind;

            fn KIND() -> IndexKind {
                IndexKind::AddressIdentifier
            }
        }

        pub mod implement_move_binary_format_file_format_ConstantPoolIndex {
            use crate::foreign_contracts::move_binary_format::file_format::IndexKind;

            fn KIND() -> IndexKind {
                IndexKind::ConstantPool
            }
        }

        pub mod implement_move_binary_format_file_format_FieldHandleIndex {
            use crate::foreign_contracts::move_binary_format::file_format::IndexKind;

            fn KIND() -> IndexKind {
                IndexKind::FieldHandle
            }
        }

        pub mod implement_move_binary_format_file_format_FieldInstantiationIndex {
            use crate::foreign_contracts::move_binary_format::file_format::IndexKind;

            fn KIND() -> IndexKind {
                IndexKind::FieldInstantiation
            }
        }

        pub mod implement_move_binary_format_file_format_FunctionHandleIndex {
            use crate::foreign_contracts::move_binary_format::file_format::IndexKind;

            fn KIND() -> IndexKind {
                IndexKind::FunctionHandle
            }
        }

        pub mod implement_move_binary_format_file_format_FunctionInstantiationIndex {
            use crate::foreign_contracts::move_binary_format::file_format::IndexKind;

            fn KIND() -> IndexKind {
                IndexKind::FunctionInstantiation
            }
        }

        pub mod implement_move_binary_format_file_format_IdentifierIndex {
            use crate::foreign_contracts::move_binary_format::file_format::IndexKind;

            fn KIND() -> IndexKind {
                IndexKind::Identifier
            }
        }

        pub mod implement_move_binary_format_file_format_ModuleHandleIndex {
            use crate::foreign_contracts::move_binary_format::file_format::IndexKind;

            fn KIND() -> IndexKind {
                IndexKind::ModuleHandle
            }
        }

        pub mod implement_move_binary_format_file_format_SignatureIndex {
            use crate::foreign_contracts::move_binary_format::file_format::IndexKind;

            fn KIND() -> IndexKind {
                IndexKind::Signature
            }
        }

        pub mod implement_move_binary_format_file_format_StructDefinitionIndex {
            use crate::foreign_contracts::move_binary_format::file_format::IndexKind;

            fn KIND() -> IndexKind {
                IndexKind::StructDefinition
            }
        }

        pub mod implement_move_binary_format_file_format_StructHandleIndex {
            use crate::foreign_contracts::move_binary_format::file_format::IndexKind;

            fn KIND() -> IndexKind {
                IndexKind::StructHandle
            }
        }

        pub mod implement_move_binary_format_file_format_StructDefInstantiationIndex {
            use crate::foreign_contracts::move_binary_format::file_format::IndexKind;

            fn KIND() -> IndexKind {
                IndexKind::StructDefInstantiation
            }
        }
    }
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
            default_contract!(unlock_slow);
        }
    }
}

pub mod proc_macro {
    pub mod implement_proc_macro_Ident {
        default_contract!(to_string);
    }

    pub mod implement_proc_macro_Span {
        default_contract!(call_site);
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

pub mod regex {
    pub mod re_unicode {
        pub mod implement_regex_re_unicode_Regex {
            default_contract!(captures);
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

pub mod ref_cast {
    pub mod layout {
        pub mod LayoutUnsized {
            pub fn ALIGN() -> usize {
                usize::MAX
            }
            pub fn SIZE() -> usize {
                usize::MAX
            }
        }
    }
}

pub mod rpds {
    pub mod map {
        pub mod red_black_tree_map {
            pub mod implement {
                pub mod insert {
                    default_contract!(ins);
                }
            }
            pub mod implement_rpds_map_red_black_tree_map_Node_generic_par_K_generic_par_V_generic_par_P {
                default_contract!(balance);
            }
            pub mod iter_utils {
                default_contract!(conservative_height);
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
    pub mod mir {
        pub mod terminator {
            pub mod implement_rustc_middle_mir_terminator_Terminator {
                default_contract!(successors);
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
                default_contract!(intern_poly_existential_predicates);
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
            pub mod QueryEngine {
                default_contract!(opt_def_kind);
                default_contract!(promoted_mir);
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
        pub mod util {
            pub mod implement_rustc_middle_ty_context_TyCtxt {
                default_contract!(is_closure);
                default_contract!(typeck_root_def_id);
            }
        }
    }
    pub mod util {
        pub mod bug {
            default_contract!(bug_fmt);
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
            pub mod implement {
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

pub mod serde {
    pub mod de {
        pub mod utf8 {
            pub fn TAG_CONT() -> u8 {
                0b1000_0000
            }
            pub fn TAG_TWO_B() -> u8 {
                0b1100_0000
            }
            pub fn TAG_THREE_B() -> u8 {
                0b1110_0000
            }
            pub fn TAG_FOUR_B() -> u8 {
                0b1111_0000
            }
            pub fn MAX_ONE_B() -> u32 {
                0x80
            }
            pub fn MAX_TWO_B() -> u32 {
                0x800
            }
            pub fn MAX_THREE_B() -> u32 {
                0x10000
            }
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
            default_contract!(capture);
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
        default_contract!(temp_dir);
        default_contract!(_var);
        default_contract!(_var_os);
        default_contract!(vars_os);

        pub mod implement_std_env_VarsOs {
            default_contract!(next);
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
            pub mod implement {
                default_contract!(into_string);
            }
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

                default_contract!(to_str);
            }
            pub mod implement_std_ffi_os_str_OsString {
                default_contract!(eq);
                default_contract!(into_string);
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
        pub mod implement_std_fs_DirBuilder {
            default_contract!(_create);
            default_contract!(new);
            default_contract!(recursive);
        }

        pub mod implement_std_fs_File {
            use std::fs::File;

            pub fn read(_self: &mut File, _buf: &mut [u8]) -> std::io::Result<usize> {
                // for i in 0..buf.len() {
                //     buf[i] = abstract_value!(0);
                // }
                result!()
            }

            default_contract!(seek);
            default_contract!(write);
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

            default_contract!(new);

            default_contract!(_open);

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

        default_contract!(read);
        default_contract!(read_to_string);
        default_contract!(write);
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

                default_contract!(new_const);
                default_contract!(last_os_error);

                pub fn _new(
                    kind: std::io::ErrorKind,
                    error: Box<dyn std::error::Error + Send + Sync>,
                ) -> Error {
                    Error {
                        repr: Repr::Custom(Box::new(Custom { kind, error })),
                    }
                }
            }
        }
        pub mod implement {
            default_contract!(drop);
        }
        pub mod stdio {
            default_contract!(_eprint);
            default_contract!(_print);
            default_contract!(set_output_capture);
        }
        pub mod Read {
            default_contract!(read);
        }
    }

    pub mod net {
        pub mod addr {
            pub mod implement_std_net_addr_SocketAddr {
                default_contract!(to_socket_addrs);
            }

            pub mod implement_tuple_2_ref_str_u16 {
                default_contract!(to_socket_addrs);
            }
        }

        pub mod ip {
            pub mod implement_std_net_ip_Ipv4Addr {
                default_contract!(cmp);
                default_contract!(from);
                default_contract!(from_inner);
                default_contract!(partial_cmp);
            }

            pub mod implement_std_net_ip_Ipv6Addr {
                default_contract!(cmp);
                default_contract!(from);
                default_contract!(from_inner);
                default_contract!(partial_cmp);
            }

            pub mod implement_u32 {
                default_contract!(from);
            }
        }

        pub mod parser {
            pub mod implement_std_net_ip_IpAddr {
                default_contract!(from_str);
            }
        }

        pub mod tcp {
            pub mod implement {
                default_contract!(set_read_timeout);
                default_contract!(set_write_timeout);
                default_contract!(shutdown);
            }

            pub mod implement_std_net_tcp_TcpStream {
                default_contract!(read);
                default_contract!(write);
            }
        }
    }

    pub mod panicking {
        pub mod panic_count {
            default_contract!(is_zero_slow_path);
        }

        default_contract!(set_hook);
        default_contract!(take_hook);
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

        pub mod implement_std_path_Components {
            default_contract!(next_back);
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

            default_contract!(_join);
            default_contract!(_with_extension);
            default_contract!(components);
            default_contract!(is_absolute);
            default_contract!(file_name);
            default_contract!(parent);
            default_contract!(to_str);
        }

        pub mod implement_std_path_PathBuf {
            default_contract!(default);
            default_contract!(from_str);
            default_contract!(_push);
            default_contract!(_set_extension);
        }
    }

    pub mod result {}

    pub mod std_detect {
        pub mod detect {
            pub mod cache {
                default_contract!(test);
            }
        }
    }

    pub mod sync {
        pub mod condvar {
            pub mod implement_std_sync_condvar_Condvar {
                default_contract!(new);
                default_contract!(notify_one);
            }
        }
        pub mod mpsc {
            pub mod blocking {
                pub mod implement_std_sync_mpsc_blocking_SignalToken {
                    default_contract!(signal);
                }
            }
            pub mod sync {
                pub mod implement_std_sync_mpsc_sync_Queue {
                    default_contract!(dequeue);
                }
            }
        }
        pub mod poison {
            pub mod implement {
                use std::sync::atomic::AtomicBool;

                pub struct Flag {
                    failed: AtomicBool,
                }

                pub fn new() -> Flag {
                    Flag {
                        failed: AtomicBool::new(false),
                    }
                }
            }
        }
    }

    pub mod sys {
        pub mod unix {
            pub mod fast_thread_local {
                default_contract!(register_dtor);
            }

            pub mod fs {
                default_contract!(stat);
            }

            pub mod memchr {
                default_contract!(memchr);
            }

            pub mod os_str {
                pub mod implement_std_sys_unix_os_str_Buf {
                    default_contract!(from_string);
                }
                pub mod implement_std_sys_unix_os_str_Slice {
                    default_contract!(to_string_lossy);
                }
            }

            pub mod thread_local_dtor {
                default_contract!(register_dtor);
            }

            pub mod thread {
                pub mod implement_std_sys_unix_thread_Thread {
                    default_contract!(join);
                    default_contract!(new);
                }
            }
        }
    }

    pub mod sys_common {
        pub mod mutex {
            pub mod implement_std_sys_common_mutex_MovableMutex {
                default_contract!(drop);
                default_contract!(new);
            }
        }

        pub mod net {
            pub mod implement_std_sys_common_net_TcpListener {
                default_contract!(bind);
            }
        }

        pub mod os_str_bytes {
            pub mod implement_std_sys_common_os_str_bytes_Buf {
                default_contract!(into_string);
                default_contract!(into_string_lossy);
            }
        }

        pub mod poison {
            pub mod implement {
                default_contract!(new);
            }
        }

        pub mod thread {
            default_contract!(min_stack);
        }

        pub mod thread_parker {
            pub mod generic {
                pub mod implement {
                    default_contract!(unpark);
                }
            }
        }
    }

    pub mod thread {
        default_contract!(current);
        default_contract!(park);
        default_contract!(yield_now);
        pub mod implement {
            default_contract!(new);
        }
        pub mod implement_std_thread_Thread {
            default_contract!(id);
            default_contract!(new);
        }
        pub mod implement_std_thread_ThreadId {
            default_contract!(as_u64);
        }
    }

    pub mod time {
        pub mod implement {
            default_contract!(checked_add);
            default_contract!(checked_duration_since);
            default_contract!(duration);
            default_contract!(elapsed);
            default_contract!(now);
        }
        pub mod implement_std_time_Instant {
            default_contract!(add);
            default_contract!(sub);
        }
        pub mod implement_std_time_SystemTime {
            default_contract!(duration);
            default_contract!(duration_since);
            default_contract!(elapsed);
            default_contract!(now);
        }
    }
}

pub mod std_detect {
    pub mod detect {
        pub mod cache {
            default_contract!(detect_and_initialize);
        }
    }
}

pub mod syn {
    pub mod attr {
        pub mod implement {
            default_contract!(parse_meta);
        }
    }

    pub mod error {
        pub mod implement {
            default_contract!(to_compile_error);
        }
    }

    pub mod lit {
        pub mod implement {
            default_contract!(parse);
        }
    }

    pub mod parse_macro_input {
        default_contract!(parse);
    }

    pub mod spanned {
        pub mod implement {
            default_contract!(span);
        }
    }
}

pub mod tinyvec {
    pub mod array {
        pub mod generated_impl {
            pub mod implement_array_generic_par_T {
                default_contract!(CAPACITY);
            }
        }
    }
}

pub mod tracing {
    pub mod __macro_support {
        pub mod implement {
            default_contract!(is_enabled);
            default_contract!(register);
        }
    }

    pub mod span {
        pub mod implement {
            default_contract!(drop);
            default_contract!(new);
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

    pub mod subscriber {
        pub mod Subscriber {
            default_contract!(enter);
            default_contract!(exit);
        }
    }
}

pub mod z3_sys {
    default_contract!(Z3_mk_bool_sort);
    default_contract!(Z3_mk_config);
    default_contract!(Z3_mk_context);
    default_contract!(Z3_mk_func_decl);
    default_contract!(Z3_mk_int);
    default_contract!(Z3_mk_int_sort);
    default_contract!(Z3_mk_solver);
    default_contract!(Z3_mk_string_symbol);
    default_contract!(Z3_mk_uninterpreted_sort);
    default_contract!(Z3_set_param_value);
    default_contract!(Z3_mk_fpa_round_nearest_ties_to_even);
    default_contract!(Z3_mk_fpa_sort_32);
    default_contract!(Z3_mk_fpa_sort_64);
}
