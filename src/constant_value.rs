// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use expression::Expression;
use rustc::hir::def_id::DefId;
use rustc::ty::TyCtxt;
use std::collections::HashMap;
use summaries::PersistentSummaryCache;
use utils::is_rust_intrinsic;

/// Abstracts over constant values referenced in MIR and adds information
/// that is useful for the abstract interpreter. More importantly, this
/// value can be serialized to the persistent summary cache.

#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialOrd, PartialEq, Hash)]
pub enum ConstantValue {
    /// The primitive character type; holds a Unicode scalar value (a non-surrogate code point).
    Char(char),
    /// The Boolean value false.
    False,
    /// A reference to a function.
    Function {
        /// The crate specific key that is used to identify the function in the current crate.
        /// This is not available for functions returned by calls to functions from other crates,
        /// since the def id the other crates use have no meaning for the current crate.
        #[serde(skip)]
        def_id: Option<DefId>,
        /// Indicates if the function is known to be treated specially by the Rust compiler
        is_intrinsic: bool,
        /// The key to use when retrieving a summary for the function from the summary cache
        summary_cache_key: String,
    },
    /// Signed 16 byte integer.
    I128(i128),
    /// 64 bit floating point, stored as a u64 to make it comparable.
    F64(u64),
    /// 32 bit floating point, stored as a u32 to make it comparable.
    F32(u32),
    /// A string literal.
    Str(String),
    /// The Boolean true value.
    True,
    /// Unsigned 16 byte integer.
    U128(u128),
    /// A place holder for other kinds of constants. Eventually this goes away.
    Unimplemented,
}

impl ConstantValue {
    /// Returns a constant value that is a reference to a function
    pub fn for_function(
        def_id: DefId,
        tcx: &TyCtxt,
        summary_cache: &mut PersistentSummaryCache,
    ) -> ConstantValue {
        let summary_cache_key = summary_cache.get_summary_key_for(def_id);
        ConstantValue::Function {
            def_id: Some(def_id),
            is_intrinsic: is_rust_intrinsic(def_id, tcx),
            summary_cache_key: summary_cache_key.to_owned(),
        }
    }
}

//todo: make ConstantValue into a domain and implement transfer functions.
//Do this by factoring out all constant related logic from AbstractDomain.

/// Keeps track of MIR constants that have already been mapped onto ConstantValue instances.
pub struct ConstantValueCache {
    char_cache: HashMap<char, ConstantValue>,
    function_cache: HashMap<DefId, ConstantValue>,
    f32_cache: HashMap<u32, ConstantValue>,
    f64_cache: HashMap<u64, ConstantValue>,
    i128_cache: HashMap<i128, ConstantValue>,
    u128_cache: HashMap<u128, ConstantValue>,
    str_cache: HashMap<String, ConstantValue>,
    std_intrinsics_unreachable_function: Option<ConstantValue>,
    std_panicking_panic_function: Option<ConstantValue>,
    heap_address_counter: usize,
}

impl ConstantValueCache {
    pub fn new() -> ConstantValueCache {
        ConstantValueCache {
            char_cache: HashMap::default(),
            function_cache: HashMap::default(),
            f32_cache: HashMap::default(),
            f64_cache: HashMap::default(),
            i128_cache: HashMap::default(),
            u128_cache: HashMap::default(),
            str_cache: HashMap::default(),
            std_intrinsics_unreachable_function: None,
            std_panicking_panic_function: None,
            heap_address_counter: 0,
        }
    }

    /// Returns a Expression::AbstractHeapAddress with a unique counter value.
    pub fn get_new_heap_address(&mut self) -> Expression {
        let heap_address_counter = self.heap_address_counter;
        self.heap_address_counter += 1;
        Expression::AbstractHeapAddress(heap_address_counter)
    }

    /// Returns a reference to a cached Expression::Char(value).
    pub fn get_char_for(&mut self, value: char) -> &ConstantValue {
        self.char_cache
            .entry(value)
            .or_insert_with(|| ConstantValue::Char(value))
    }

    /// Returns a reference to a cached Expression::F32(value).
    pub fn get_f32_for(&mut self, value: u32) -> &ConstantValue {
        self.f32_cache
            .entry(value)
            .or_insert_with(|| ConstantValue::F32(value))
    }

    /// Returns a reference to a cached Expression::F64(value).
    pub fn get_f64_for(&mut self, value: u64) -> &ConstantValue {
        self.f64_cache
            .entry(value)
            .or_insert_with(|| ConstantValue::F64(value))
    }

    /// Returns a reference to a cached Expression::I128(value).
    pub fn get_i128_for(&mut self, value: i128) -> &ConstantValue {
        self.i128_cache
            .entry(value)
            .or_insert_with(|| ConstantValue::I128(value))
    }

    pub fn get_string_for(&mut self, value: &str) -> &ConstantValue {
        let str_value = String::from(value);
        self.str_cache
            .entry(str_value)
            .or_insert_with(|| ConstantValue::Str(String::from(value)))
    }

    /// Returns a reference to a cached Expression::U128(value).
    pub fn get_u128_for(&mut self, value: u128) -> &ConstantValue {
        self.u128_cache
            .entry(value)
            .or_insert_with(|| ConstantValue::U128(value))
    }

    /// Given the MIR DefId of a function return the unique (cached) ConstantValue that corresponds
    /// to the function identified by that DefId.
    pub fn get_function_constant_for(
        &mut self,
        def_id: DefId,
        tcx: &TyCtxt,
        summary_cache: &mut PersistentSummaryCache,
    ) -> &ConstantValue {
        self.function_cache
            .entry(def_id)
            .or_insert_with(|| ConstantValue::for_function(def_id, tcx, summary_cache))
    }

    /// Does an expensive check to see if the given function is std::intrinsics::unreachable.
    /// Once it finds the function it caches it so that subsequent checks are cheaper.
    pub fn check_if_std_intrinsics_unreachable_function(&mut self, fun: &ConstantValue) -> bool {
        let result = self
            .std_intrinsics_unreachable_function
            .as_ref()
            .map(|std_fun| *std_fun == *fun);
        result.unwrap_or_else(|| {
            let result = match fun {
                ConstantValue::Function {
                    is_intrinsic,
                    summary_cache_key,
                    ..
                } => *is_intrinsic && summary_cache_key.ends_with("unreachable"),
                _ => false,
            };
            if result {
                self.std_intrinsics_unreachable_function = Some(fun.clone());
            };
            result
        })
    }

    /// Does an expensive check to see if the given function is std.panicking.begin_panic.
    /// Once it finds the function it caches it so that subsequent checks are cheaper.
    pub fn check_if_std_panicking_begin_panic_function(&mut self, fun: &ConstantValue) -> bool {
        let result = self
            .std_panicking_panic_function
            .as_ref()
            .map(|std_fun| *std_fun == *fun);
        result.unwrap_or_else(|| {
            let result = match fun {
                ConstantValue::Function {
                    summary_cache_key, ..
                } => summary_cache_key == "std.panicking.begin_panic",
                _ => false,
            };
            if result {
                self.std_panicking_panic_function = Some(fun.clone());
            };
            result
        })
    }
}

impl Default for ConstantValueCache {
    fn default() -> Self {
        Self::new()
    }
}
