// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a loop counter incremented via a for-in.

#![feature(type_alias_enum_variants)]
#![allow(non_snake_case)]
#![allow(non_camel_case_types)]

#[macro_use]
extern crate mirai_annotations;

pub mod foreign_contracts {
    pub mod core {

        pub mod default {
            pub trait Default {
                fn default_() {
                    result!()
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
            pub mod traits {
                pub mod collect {
                    use crate::foreign_contracts::core::ops::range::implement_12::RangeInclusive_usize;

                    pub trait IntoIterator {
                        fn into_iter__core_ops_range_RangeInclusive_usize(
                            range: RangeInclusive_usize,
                        ) -> RangeInclusive_usize {
                            range
                        }
                    }
                }

                pub mod iterator {
                    use crate::foreign_contracts::core::ops::range::implement_12::{
                        compute_is_empty__usize, RangeInclusive_usize,
                    };

                    pub trait Iterator {
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
                    }
                }
            }
        }

    }
}

pub fn foo(n: usize) {
    for ordinal in 2..=n {
        verify!(ordinal - 1 >= 1);
    }
}

pub fn main() {}
