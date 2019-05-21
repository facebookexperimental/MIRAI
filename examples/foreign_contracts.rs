#![allow(non_snake_case)]
#![allow(non_camel_case_types)]

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
            fn lt__ref_ref_i32_ref_ref_i32(x: &i32, y: &i32) -> bool {
                (*x) < (*y)
            }
        }

        pub trait Ord {
            fn cmp<T>(_a: &T, _b: &T) -> Ordering {
                result!()
            }
        }
    }

    pub mod default {
        pub trait Default {
            fn default_() {
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

        pub mod implement_1 {
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

        pub mod implement_2 {
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

        pub mod implement_5 {
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
            pub mod implement_12 {
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

                pub fn new__usize_usize(start: usize, end: usize) -> RangeInclusive_usize {
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
    }

    pub mod iter {
        pub mod adapters {
            use crate::foreign_contracts::core::ops::range::implement_12::Range_usize;
            use crate::foreign_contracts::core::slice::Iter;

            pub struct Enumerator_slice<'a, T: 'a> {
                pub iterator: Iter<'a, T>,
            }

            pub struct Rev__Range_usize {
                pub range: Range_usize,
            }
        }

        pub mod traits {
            pub mod collect {
                use crate::foreign_contracts::core::iter::adapters::Enumerator_slice;
                use crate::foreign_contracts::core::ops::range::implement_12::RangeInclusive_usize;
                use crate::foreign_contracts::core::ops::range::implement_12::Range_usize;

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
                use crate::foreign_contracts::core::ops::range::implement_12::compute_is_empty__usize;
                use crate::foreign_contracts::core::ops::range::implement_12::RangeInclusive_usize;
                use crate::foreign_contracts::core::ops::range::implement_12::Range_usize;
                use crate::foreign_contracts::core::slice::Iter;

                pub trait Iterator {
                    fn enumerate__core_slice_Iter_bool(iter: Iter<bool>) -> Enumerator_slice<bool> {
                        Enumerator_slice { iterator: iter }
                    }

                    fn next__ref_mut_core_iter_adapters_Enumerate_core_slice_Iter_bool(
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

                    fn next__ref_mut_core_ops_range_Range_usize(
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

                    fn next__ref_mut_core_ops_range_RangeInclusive_usize(
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

                    fn next_back__ref_mut_core_ops_range_Range_usize(
                        range: &mut Range_usize,
                    ) -> Option<usize> {
                        if range.start < range.end {
                            range.end -= 1;
                            Some(range.end)
                        } else {
                            None
                        }
                    }

                    fn next__ref_mut_core_iter_adapters_Rev_core_ops_range_Range_usize(
                        rev: &mut Rev__Range_usize,
                    ) -> Option<usize> {
                        Self::next_back__ref_mut_core_ops_range_Range_usize(&mut rev.range)
                    }

                    fn rev__core_ops_range_Range_usize(range: Range_usize) -> Rev__Range_usize {
                        Rev__Range_usize { range }
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
            pub fn iter__ref_slice_bool(collection: &[bool]) -> Iter<bool> {
                Iter {
                    collection,
                    index: 0,
                }
            }

            pub fn len__ref_slice_bool(collection: &[bool]) -> usize {
                collection.len()
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
