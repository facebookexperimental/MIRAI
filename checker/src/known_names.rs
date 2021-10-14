// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use rustc_hir::def_id::DefId;
use rustc_hir::definitions::{DefPathData, DisambiguatedDefPathData};
use rustc_middle::ty::TyCtxt;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Well known definitions (language provided items) that are treated in special ways.
#[derive(Serialize, Deserialize, Clone, Copy, Debug, Eq, PartialOrd, PartialEq, Hash, Ord)]
pub enum KnownNames {
    /// This is not a known name
    None,
    AllocRawVecMinNonZeroCap,
    MiraiAbstractValue,
    MiraiAddTag,
    MiraiAssume,
    MiraiAssumePreconditions,
    MiraiDoesNotHaveTag,
    MiraiGetModelField,
    MiraiHasTag,
    MiraiPostcondition,
    MiraiPrecondition,
    MiraiPreconditionStart,
    MiraiResult,
    MiraiSetModelField,
    MiraiVerify,
    RustAlloc,
    RustAllocZeroed,
    RustDealloc,
    RustRealloc,
    StdCloneClone,
    StdFutureFromGenerator,
    StdIntrinsicsArithOffset,
    StdIntrinsicsBitreverse,
    StdIntrinsicsBswap,
    StdIntrinsicsCeilf32,
    StdIntrinsicsCeilf64,
    StdIntrinsicsCopy,
    StdIntrinsicsCopyNonOverlapping,
    StdIntrinsicsCopysignf32,
    StdIntrinsicsCopysignf64,
    StdIntrinsicsCosf32,
    StdIntrinsicsCosf64,
    StdIntrinsicsCtlz,
    StdIntrinsicsCtlzNonzero,
    StdIntrinsicsCtpop,
    StdIntrinsicsCttz,
    StdIntrinsicsCttzNonzero,
    StdIntrinsicsDiscriminantValue,
    StdIntrinsicsExp2f32,
    StdIntrinsicsExp2f64,
    StdIntrinsicsExpf32,
    StdIntrinsicsExpf64,
    StdIntrinsicsFabsf32,
    StdIntrinsicsFabsf64,
    StdIntrinsicsFaddFast,
    StdIntrinsicsFdivFast,
    StdIntrinsicsFloorf32,
    StdIntrinsicsFloorf64,
    StdIntrinsicsFmulFast,
    StdIntrinsicsFremFast,
    StdIntrinsicsFsubFast,
    StdIntrinsicsLog10f32,
    StdIntrinsicsLog10f64,
    StdIntrinsicsLog2f32,
    StdIntrinsicsLog2f64,
    StdIntrinsicsLogf32,
    StdIntrinsicsLogf64,
    StdIntrinsicsMaxnumf32,
    StdIntrinsicsMaxnumf64,
    StdIntrinsicsMinAlignOfVal,
    StdIntrinsicsMinnumf32,
    StdIntrinsicsMinnumf64,
    StdIntrinsicsMulWithOverflow,
    StdIntrinsicsNearbyintf32,
    StdIntrinsicsNearbyintf64,
    StdIntrinsicsOffset,
    StdIntrinsicsPowf32,
    StdIntrinsicsPowf64,
    StdIntrinsicsPowif32,
    StdIntrinsicsPowif64,
    StdIntrinsicsRawEq,
    StdIntrinsicsRintf32,
    StdIntrinsicsRintf64,
    StdIntrinsicsRoundf32,
    StdIntrinsicsRoundf64,
    StdIntrinsicsSinf32,
    StdIntrinsicsSinf64,
    StdIntrinsicsSizeOf,
    StdIntrinsicsSizeOfVal,
    StdIntrinsicsSqrtf32,
    StdIntrinsicsSqrtf64,
    StdIntrinsicsTransmute,
    StdIntrinsicsTruncf32,
    StdIntrinsicsTruncf64,
    StdIntrinsicsWriteBytes,
    StdMarkerPhantomData,
    StdMemReplace,
    StdOpsFunctionFnCall,
    StdOpsFunctionFnMutCallMut,
    StdOpsFunctionFnOnceCallOnce,
    StdPanickingAssertFailed,
    StdPanickingBeginPanic,
    StdPanickingBeginPanicFmt,
    StdPtrSwapNonOverlapping,
    StdSliceCmpMemcmp,
}

/// An analysis lifetime cache that contains a map from def ids to known names.
pub struct KnownNamesCache {
    name_cache: HashMap<DefId, KnownNames>,
}

type Iter<'a> = std::slice::Iter<'a, rustc_hir::definitions::DisambiguatedDefPathData>;

impl KnownNamesCache {
    /// Create an empty known names cache.
    /// This cache is re-used by every successive MIR visitor instance.
    pub fn create_cache_from_language_items() -> KnownNamesCache {
        let name_cache = HashMap::new();
        KnownNamesCache { name_cache }
    }

    /// Get the well known name for the given def id and cache the association.
    /// I.e. the first call for an unknown def id will be somewhat costly but
    /// subsequent calls will be cheap. If the def_id does not have an actual well
    /// known name, this returns KnownNames::None.
    pub fn get(&mut self, tcx: TyCtxt<'_>, def_id: DefId) -> KnownNames {
        *self
            .name_cache
            .entry(def_id)
            .or_insert_with(|| Self::get_known_name_for(tcx, def_id))
    }

    /// Uses information obtained from tcx to figure out which well known name (if any)
    /// this def id corresponds to.
    fn get_known_name_for(tcx: TyCtxt<'_>, def_id: DefId) -> KnownNames {
        use std::ops::Deref;
        use DefPathData::*;

        let def_path = &tcx.def_path(def_id);
        let def_path_data_iter = def_path.data.iter();

        // helper to get next elem from def path and return its name, if it has one
        let get_path_data_elem_name =
            |def_path_data_elem: Option<&rustc_hir::definitions::DisambiguatedDefPathData>| {
                def_path_data_elem.and_then(|ref elem| {
                    let DisambiguatedDefPathData { data, .. } = elem;
                    match &data {
                        TypeNs(name) | ValueNs(name) => Some(*name),
                        _ => None,
                    }
                })
            };

        let path_data_elem_as_disambiguator = |def_path_data_elem: Option<
            &rustc_hir::definitions::DisambiguatedDefPathData,
        >| {
            def_path_data_elem.map(|DisambiguatedDefPathData { disambiguator, .. }| *disambiguator)
        };

        let get_known_name_for_alloc_namespace =
            |mut def_path_data_iter: Iter<'_>| match get_path_data_elem_name(
                def_path_data_iter.next(),
            ) {
                Some(n) if n.as_str().deref() == "" => {
                    get_path_data_elem_name(def_path_data_iter.next())
                        .map(|n| match n.as_str().deref() {
                            "__rust_alloc" => KnownNames::RustAlloc,
                            "__rust_alloc_zeroed" => KnownNames::RustAllocZeroed,
                            "__rust_dealloc" => KnownNames::RustDealloc,
                            "__rust_realloc" => KnownNames::RustRealloc,
                            _ => KnownNames::None,
                        })
                        .unwrap_or(KnownNames::None)
                }
                _ => KnownNames::None,
            };

        let get_known_name_for_clone_trait = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str().deref() {
                    "clone" => KnownNames::StdCloneClone,
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_clone_namespace = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str().deref() {
                    "Clone" => get_known_name_for_clone_trait(def_path_data_iter),
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_future_namespace = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str().deref() {
                    "from_generator" => KnownNames::StdFutureFromGenerator,
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_intrinsics_namespace = |mut def_path_data_iter: Iter<'_>| {
            let current_elem = def_path_data_iter.next();
            match path_data_elem_as_disambiguator(current_elem) {
                Some(0) => get_path_data_elem_name(current_elem)
                    .map(|n| match n.as_str().deref() {
                        "copy" => KnownNames::StdIntrinsicsCopy,
                        "copy_nonoverlapping" => KnownNames::StdIntrinsicsCopyNonOverlapping,
                        "write_bytes" => KnownNames::StdIntrinsicsWriteBytes,
                        _ => KnownNames::None,
                    })
                    .unwrap_or(KnownNames::None),
                Some(1) => get_path_data_elem_name(def_path_data_iter.next())
                    .map(|n| match n.as_str().deref() {
                        "arith_offset" => KnownNames::StdIntrinsicsArithOffset,
                        "bitreverse" => KnownNames::StdIntrinsicsBitreverse,
                        "bswap" => KnownNames::StdIntrinsicsBswap,
                        "ceilf32" => KnownNames::StdIntrinsicsCeilf32,
                        "ceilf64" => KnownNames::StdIntrinsicsCeilf64,
                        "copysignf32" => KnownNames::StdIntrinsicsCopysignf32,
                        "copysignf64" => KnownNames::StdIntrinsicsCopysignf64,
                        "cosf32" => KnownNames::StdIntrinsicsCosf32,
                        "cosf64" => KnownNames::StdIntrinsicsCosf64,
                        "ctlz" => KnownNames::StdIntrinsicsCtlz,
                        "ctlz_nonzero" => KnownNames::StdIntrinsicsCtlzNonzero,
                        "ctpop" => KnownNames::StdIntrinsicsCtpop,
                        "cttz" => KnownNames::StdIntrinsicsCttz,
                        "cttz_nonzero" => KnownNames::StdIntrinsicsCttzNonzero,
                        "discriminant_value" => KnownNames::StdIntrinsicsDiscriminantValue,
                        "exp2f32" => KnownNames::StdIntrinsicsExp2f32,
                        "exp2f64" => KnownNames::StdIntrinsicsExp2f64,
                        "expf32" => KnownNames::StdIntrinsicsExpf32,
                        "expf64" => KnownNames::StdIntrinsicsExpf64,
                        "fabsf32" => KnownNames::StdIntrinsicsFabsf32,
                        "fabsf64" => KnownNames::StdIntrinsicsFabsf64,
                        "fadd_fast" => KnownNames::StdIntrinsicsFaddFast,
                        "fdiv_fast" => KnownNames::StdIntrinsicsFdivFast,
                        "floorf32" => KnownNames::StdIntrinsicsFloorf32,
                        "floorf64" => KnownNames::StdIntrinsicsFloorf64,
                        "fmul_fast" => KnownNames::StdIntrinsicsFmulFast,
                        "frem_fast" => KnownNames::StdIntrinsicsFremFast,
                        "fsub_fast" => KnownNames::StdIntrinsicsFsubFast,
                        "log10f32" => KnownNames::StdIntrinsicsLog10f32,
                        "log10f64" => KnownNames::StdIntrinsicsLog10f64,
                        "log2f32" => KnownNames::StdIntrinsicsLog2f32,
                        "log2f64" => KnownNames::StdIntrinsicsLog2f64,
                        "logf32" => KnownNames::StdIntrinsicsLogf32,
                        "logf64" => KnownNames::StdIntrinsicsLogf64,
                        "maxnumf32" => KnownNames::StdIntrinsicsMaxnumf32,
                        "maxnumf64" => KnownNames::StdIntrinsicsMaxnumf64,
                        "min_align_of_val" => KnownNames::StdIntrinsicsMinAlignOfVal,
                        "minnumf32" => KnownNames::StdIntrinsicsMinnumf32,
                        "minnumf64" => KnownNames::StdIntrinsicsMinnumf64,
                        "mul_with_overflow" => KnownNames::StdIntrinsicsMulWithOverflow,
                        "nearbyintf32" => KnownNames::StdIntrinsicsNearbyintf32,
                        "nearbyintf64" => KnownNames::StdIntrinsicsNearbyintf64,
                        "offset" => KnownNames::StdIntrinsicsOffset,
                        "powf32" => KnownNames::StdIntrinsicsPowf32,
                        "powf64" => KnownNames::StdIntrinsicsPowf64,
                        "powif32" => KnownNames::StdIntrinsicsPowif32,
                        "powif64" => KnownNames::StdIntrinsicsPowif64,
                        "raw_eq" => KnownNames::StdIntrinsicsRawEq,
                        "rintf32" => KnownNames::StdIntrinsicsRintf32,
                        "rintf64" => KnownNames::StdIntrinsicsRintf64,
                        "roundf32" => KnownNames::StdIntrinsicsRintf32,
                        "roundf64" => KnownNames::StdIntrinsicsRintf64,
                        "sinf32" => KnownNames::StdIntrinsicsSinf32,
                        "sinf64" => KnownNames::StdIntrinsicsSinf64,
                        "size_of" => KnownNames::StdIntrinsicsSizeOf,
                        "size_of_val" => KnownNames::StdIntrinsicsSizeOfVal,
                        "sqrtf32" => KnownNames::StdIntrinsicsSqrtf32,
                        "sqrtf64" => KnownNames::StdIntrinsicsSqrtf64,
                        "transmute" => KnownNames::StdIntrinsicsTransmute,
                        "truncf32" => KnownNames::StdIntrinsicsTruncf32,
                        "truncf64" => KnownNames::StdIntrinsicsTruncf64,
                        _ => KnownNames::None,
                    })
                    .unwrap_or(KnownNames::None),
                _ => KnownNames::None,
            }
        };

        let get_known_name_for_marker_namespace = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str().deref() {
                    "PhantomData" => KnownNames::StdMarkerPhantomData,
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_mem_namespace = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str().deref() {
                    "replace" => KnownNames::StdMemReplace,
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_ops_function_namespace = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str().deref() {
                    "Fn" | "FnMut" | "FnOnce" => get_path_data_elem_name(def_path_data_iter.next())
                        .map(|n| match n.as_str().deref() {
                            "call" => KnownNames::StdOpsFunctionFnCall,
                            "call_mut" => KnownNames::StdOpsFunctionFnMutCallMut,
                            "call_once" => KnownNames::StdOpsFunctionFnOnceCallOnce,
                            _ => KnownNames::None,
                        })
                        .unwrap_or(KnownNames::None),
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_ops_namespace = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str().deref() {
                    "function" => get_known_name_for_ops_function_namespace(def_path_data_iter),
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_panicking_namespace = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str().deref() {
                    "assert_failed" => KnownNames::StdPanickingAssertFailed,
                    "begin_panic" | "panic" => KnownNames::StdPanickingBeginPanic,
                    "begin_panic_fmt" | "panic_fmt" => KnownNames::StdPanickingBeginPanicFmt,
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_ptr_mut_ptr_namespace =
            |mut def_path_data_iter: Iter<'_>| match path_data_elem_as_disambiguator(
                def_path_data_iter.next(),
            ) {
                Some(0) => get_path_data_elem_name(def_path_data_iter.next())
                    .map(|n| match n.as_str().deref() {
                        "write_bytes" => KnownNames::StdIntrinsicsWriteBytes,
                        _ => KnownNames::None,
                    })
                    .unwrap_or(KnownNames::None),
                _ => KnownNames::None,
            };

        let get_known_name_for_ptr_namespace = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str().deref() {
                    "swap_nonoverlapping" => KnownNames::StdPtrSwapNonOverlapping,
                    "mut_ptr" => get_known_name_for_ptr_mut_ptr_namespace(def_path_data_iter),
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_slice_cmp_namespace =
            |mut def_path_data_iter: Iter<'_>| match path_data_elem_as_disambiguator(
                def_path_data_iter.next(),
            ) {
                Some(0) => get_path_data_elem_name(def_path_data_iter.next())
                    .map(|n| match n.as_str().deref() {
                        "memcmp" => KnownNames::StdSliceCmpMemcmp,
                        _ => KnownNames::None,
                    })
                    .unwrap_or(KnownNames::None),
                _ => KnownNames::None,
            };

        let get_known_name_for_raw_vec_namespace =
            |mut def_path_data_iter: Iter<'_>| match path_data_elem_as_disambiguator(
                def_path_data_iter.next(),
            ) {
                Some(1) => get_path_data_elem_name(def_path_data_iter.next())
                    .map(|n| match n.as_str().deref() {
                        "MIN_NON_ZERO_CAP" => KnownNames::AllocRawVecMinNonZeroCap,
                        _ => KnownNames::None,
                    })
                    .unwrap_or(KnownNames::None),
                _ => KnownNames::None,
            };

        let get_known_name_for_slice_namespace = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str().deref() {
                    "cmp" => get_known_name_for_slice_cmp_namespace(def_path_data_iter),
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_known_crate = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str().deref() {
                    "alloc" => get_known_name_for_alloc_namespace(def_path_data_iter),
                    "clone" => get_known_name_for_clone_namespace(def_path_data_iter),
                    "future" => get_known_name_for_future_namespace(def_path_data_iter),
                    "intrinsics" => get_known_name_for_intrinsics_namespace(def_path_data_iter),
                    "marker" => get_known_name_for_marker_namespace(def_path_data_iter),
                    "mem" => get_known_name_for_mem_namespace(def_path_data_iter),
                    "ops" => get_known_name_for_ops_namespace(def_path_data_iter),
                    "panicking" => get_known_name_for_panicking_namespace(def_path_data_iter),
                    "ptr" => get_known_name_for_ptr_namespace(def_path_data_iter),
                    "mirai_abstract_value" => KnownNames::MiraiAbstractValue,
                    "mirai_add_tag" => KnownNames::MiraiAddTag,
                    "mirai_assume" => KnownNames::MiraiAssume,
                    "mirai_assume_preconditions" => KnownNames::MiraiAssumePreconditions,
                    "mirai_does_not_have_tag" => KnownNames::MiraiDoesNotHaveTag,
                    "mirai_get_model_field" => KnownNames::MiraiGetModelField,
                    "mirai_has_tag" => KnownNames::MiraiHasTag,
                    "mirai_postcondition" => KnownNames::MiraiPostcondition,
                    "mirai_precondition_start" => KnownNames::MiraiPreconditionStart,
                    "mirai_precondition" => KnownNames::MiraiPrecondition,
                    "mirai_result" => KnownNames::MiraiResult,
                    "mirai_set_model_field" => KnownNames::MiraiSetModelField,
                    "mirai_verify" => KnownNames::MiraiVerify,
                    "raw_vec" => get_known_name_for_raw_vec_namespace(def_path_data_iter),
                    "slice" => get_known_name_for_slice_namespace(def_path_data_iter),
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let crate_name = tcx.crate_name(def_id.krate);
        match crate_name.as_str().deref() {
            "alloc" | "core" | "mirai_annotations" | "std" => {
                get_known_name_for_known_crate(def_path_data_iter)
            }
            _ => KnownNames::None,
        }
    }
}
