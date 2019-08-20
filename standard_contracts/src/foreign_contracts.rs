#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(unknown_lints)]
#![allow(clippy::all)]

pub mod core {

    pub mod cmp {

        pub enum Ordering {
            /// An ordering where a compared value is less than another.
            Less = -1,
            /// An ordering where a compared value is equal to another.
            Equal = 0,
            /// An ordering where a compared value is greater than another.
            Greater = 1,
        }

        pub trait PartialOrd<Rhs: ?Sized = Self> {
            fn lt__ref_i32_ref_i32(x: &i32, y: &i32) -> bool {
                (*x) < (*y)
            }
        }

        pub trait Ord {
            fn cmp<T>(_a: &T, _b: &T) -> Ordering {
                result!()
            }
        }

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

        pub mod rt {
            pub mod v1 {
                pub struct Argument {}
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

        pub struct Formatter<'a> {
            phantom: PhantomData<&'a str>,
        }

        pub struct Result {}

        pub struct Void {}
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
                _self.checked_add(value)
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
                _self.checked_add(value)
            }
        }

        pub mod implement_u16 {
            pub fn max_value() -> u16 {
                65535
            }
            pub fn min_value() -> u16 {
                0
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
            pub fn max_value() -> u128 {
                18446744073709551615
            }
            pub fn min_value() -> u128 {
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

    pub mod option {
        pub enum Option<T> {
            None,
            Some(T),
        }

        impl<T> Option<T> {
            pub fn is_none(&self) -> bool {
                match self {
                    Self::None => true,
                    _ => false,
                }
            }

            pub fn is_some(&self) -> bool {
                match self {
                    Self::None => false,
                    _ => true,
                }
            }

            pub fn unwrap(self) -> T {
                precondition!(self.is_some(), "self may not be None");
                result!()
            }
        }

        pub mod implement_core_option_Option_T {
            use crate::foreign_contracts::core::option::Option;

            pub fn unwrap_or_default<T: Default>(v: Option<T>) -> T {
                match v {
                    Option::None => Default::default(),
                    Option::Some(v) => v,
                }
            }
        }
    }

    pub mod ops {
        pub mod range {
            pub mod implement_core_ops_range_RangeInclusive_Idx {
                pub struct Range_usize {
                    pub start: usize,
                    pub end: usize,
                }

                pub struct RangeInclusive_usize {
                    pub start: usize,
                    pub end: usize,
                    pub is_empty: Option<bool>,
                    // This field is:
                    //  - `None` when next() or next_back() was never called
                    //  - `Some(false)` when `start <= end` assuming no overflow
                    //  - `Some(true)` otherwise
                    // The field cannot be a simple `bool` because the `..=` constructor can
                    // accept non-PartialOrd types, also we want the constructor to be const.
                }

                pub fn new__usize(start: usize, end: usize) -> RangeInclusive_usize {
                    RangeInclusive_usize {
                        start,
                        end,
                        is_empty: None,
                    }
                }

                // If this range's `is_empty` is field is unknown (`None`), update it to be a concrete value.
                pub fn compute_is_empty__usize(range: &mut RangeInclusive_usize) {
                    if range.is_empty.is_none() {
                        range.is_empty = Some(!(range.start <= range.end));
                    }
                }
            }
        }

        pub mod deref {
            pub trait Deref {
                fn deref__alloc_vec_Vec_i32(vec: &Vec<i32>) -> &[i32] {
                    let old_len = vec.len();
                    let res: &[i32] = result!();
                    assume!(res.len() == old_len);
                    res
                }
                fn deref__alloc_vec_Vec_u32(vec: &Vec<u32>) -> &[u32] {
                    let old_len = vec.len();
                    let res: &[u32] = result!();
                    assume!(res.len() == old_len);
                    res
                }
            }
        }
    }

    pub mod iter {
        pub mod adapters {
            use crate::foreign_contracts::core::ops::range::implement_core_ops_range_RangeInclusive_Idx::Range_usize;
            use crate::foreign_contracts::core::slice::Iter;

            pub struct Enumerator_slice<'a, T: 'a> {
                pub iterator: Iter<'a, T>,
            }

            pub struct Rev__Range_usize {
                pub range: Range_usize,
            }

            pub struct Enumerate<I> {
                _iter: I,
                _count: usize,
            }

            impl<I> Enumerate<I> {
                pub(super) fn new(iter: I) -> Enumerate<I> {
                    Enumerate {
                        _iter: iter,
                        _count: 0,
                    }
                }
            }
        }

        pub mod traits {
            pub mod collect {
                use crate::foreign_contracts::core::iter::adapters::Enumerator_slice;
                use crate::foreign_contracts::core::ops::range::implement_core_ops_range_RangeInclusive_Idx::RangeInclusive_usize;
                use crate::foreign_contracts::core::ops::range::implement_core_ops_range_RangeInclusive_Idx::Range_usize;

                pub trait IntoIterator {
                    fn into_iter__core_iter_adapters_Enumerate_core_slice_Iter_bool(
                        slice: Enumerator_slice<bool>,
                    ) -> Enumerator_slice<bool> {
                        slice
                    }

                    fn into_iter__core_ops_range_Range_usize(range: Range_usize) -> Range_usize {
                        range
                    }

                    fn into_iter__core_ops_range_RangeInclusive_usize(
                        range: RangeInclusive_usize,
                    ) -> RangeInclusive_usize {
                        range
                    }
                }
            }

            pub mod iterator {
                use crate::foreign_contracts::core::iter::adapters::Enumerator_slice;
                use crate::foreign_contracts::core::iter::adapters::Rev__Range_usize;
                use crate::foreign_contracts::core::ops::range::implement_core_ops_range_RangeInclusive_Idx::compute_is_empty__usize;
                use crate::foreign_contracts::core::ops::range::implement_core_ops_range_RangeInclusive_Idx::RangeInclusive_usize;
                use crate::foreign_contracts::core::ops::range::implement_core_ops_range_RangeInclusive_Idx::Range_usize;
                use crate::foreign_contracts::core::slice::Iter;
                use crate::foreign_contracts::core::iter::adapters::Enumerate;

                pub trait Iterator {
                    fn enumerate__core_slice_Iter_bool(iter: Iter<bool>) -> Enumerator_slice<bool> {
                        Enumerator_slice { iterator: iter }
                    }

                    fn next__core_iter_adapters_Enumerate_core_slice_Iter_bool(
                        mut slice: &mut Enumerator_slice<bool>,
                    ) -> Option<(usize, bool)> {
                        let i = slice.iterator.index;
                        let collection = slice.iterator.collection;
                        if i < collection.len() {
                            slice.iterator.index += 1;
                            Some((i, collection[i]))
                        } else {
                            None
                        }
                    }

                    fn next__core_ops_range_Range_usize(
                        mut range: &mut Range_usize,
                    ) -> Option<usize> {
                        if range.start < range.end {
                            let n = range.start;
                            range.start = n + 1;
                            Some(n)
                        } else {
                            None
                        }
                    }

                    fn next__core_ops_range_RangeInclusive_usize(
                        mut range: &mut RangeInclusive_usize,
                    ) -> Option<usize> {
                        compute_is_empty__usize(&mut range);
                        if range.is_empty.unwrap_or_default() {
                            return None;
                        }
                        let is_iterating = range.start < range.end;
                        range.is_empty = Some(!is_iterating);
                        Some(if is_iterating {
                            let n = range.start;
                            range.start = n + 1;
                            n
                        } else {
                            range.start
                        })
                    }

                    fn next_back__core_ops_range_Range_usize(
                        range: &mut Range_usize,
                    ) -> Option<usize> {
                        if range.start < range.end {
                            range.end -= 1;
                            Some(range.end)
                        } else {
                            None
                        }
                    }

                    fn next__core_iter_adapters_Rev_core_ops_range_Range_usize(
                        rev: &mut Rev__Range_usize,
                    ) -> Option<usize> {
                        Self::next_back__core_ops_range_Range_usize(&mut rev.range)
                    }

                    fn rev__core_ops_range_Range_usize(range: Range_usize) -> Rev__Range_usize {
                        Rev__Range_usize { range }
                    }

                    fn enumerate(self) -> Enumerate<Self>
                    where
                        Self: Sized,
                    {
                        Enumerate::new(self)
                    }
                }
            }
        }
    }

    pub mod slice {
        use crate::foreign_contracts::core::iter::adapters::Enumerator_slice;

        pub struct Iter<'a, T: 'a> {
            pub collection: &'a [T],
            pub index: usize,
        }

        impl<'a, T: 'a> Iter<'a, T> {
            pub fn enumerate(self) -> Enumerator_slice<'a, T> {
                Enumerator_slice { iterator: self }
            }
        }

        pub mod implement {

            use crate::foreign_contracts::core::slice::Iter;
            pub fn iter__bool(collection: &[bool]) -> Iter<bool> {
                Iter {
                    collection,
                    index: 0,
                }
            }

            pub fn get__u32_usize(collection: &[u32], index: usize) -> Option<&u32> {
                if index >= collection.len() {
                    None
                } else {
                    Some(&collection[index])
                }
            }

            pub fn is_empty<T>(collection: &[T]) -> bool {
                collection.len() == 0
            }

            pub fn len<T>(collection: &[T]) -> usize {
                collection.len()
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

    pub mod mem {
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
    }

    pub mod str {
        pub mod implement_str {
            pub fn is_empty(_self: &str) -> bool {
                _self.len() == 0
            }
        }
    }
}

pub mod std {
    pub mod io {
        pub mod stdio {
            use crate::foreign_contracts::core::fmt;
            pub fn _print(_args: fmt::Arguments<'_>) {}
        }
    }

    pub mod result {}
}

pub mod alloc {
    pub mod slice {
        pub struct Slice<T: Clone> {
            len: usize,
            data: T,
        }
        impl<T: Clone> Slice<T> {
            pub fn into_vec(self: Box<Self>) -> Vec<T>
            where
                T: Clone,
            {
                let mut v = Vec::with_capacity(self.len);
                v.resize(self.len, self.data);
                v
            }
        }
    }
    pub mod vec {
        pub struct Vec<T> {
            _phantom: std::marker::PhantomData<T>,
            capacity: usize,
            len: usize,
        }

        impl<T> Vec<T> {
            pub fn new() -> Vec<T> {
                Vec {
                    _phantom: std::marker::PhantomData,
                    capacity: 0,
                    len: 0,
                }
            }

            pub fn with_capacity(capacity: usize) -> Vec<T> {
                Vec {
                    _phantom: std::marker::PhantomData,
                    capacity: capacity,
                    len: 0,
                }
            }

            pub fn append(&mut self, other: &mut Vec<T>) {
                precondition!(
                    self.len <= usize::max_value() - other.len(),
                    "exceeds max vector length"
                );
                self.len += other.len;
            }

            pub fn capacity(&self) -> usize {
                self.capacity
            }

            pub fn clear(&mut self) {
                self.len = 0;
            }

            pub fn is_empty(&self) -> bool {
                self.len == 0
            }

            pub fn len(&self) -> usize {
                self.len
            }

            pub fn pop(&mut self) -> Option<T> {
                if self.len == 0 {
                    None
                } else {
                    self.len -= 1;
                    result!()
                }
            }

            pub fn push(&mut self, _value: T) {
                precondition!(self.len < usize::max_value(), "exceeds max vector length");
                self.len += 1;
            }

            pub fn reserve(&mut self, additional: usize) {
                precondition!(
                    self.len < usize::max_value() - additional,
                    "exceeds max vector capacity"
                );
                let new_capacity = self.len + additional;
                if new_capacity > self.capacity {
                    self.capacity = new_capacity;
                }
            }

            pub fn resize(&mut self, new_len: usize, _value: T) {
                self.len = new_len
            }
        }
    }
}
