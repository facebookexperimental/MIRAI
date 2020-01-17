// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use rustc::hir::map::{DefPathData, DisambiguatedDefPathData};
use rustc::ty::TyCtxt;
use rustc_hir::def_id::DefId;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Well known definitions (language provided items) that are treated in special ways.
#[derive(Serialize, Deserialize, Clone, Copy, Debug, Eq, PartialOrd, PartialEq, Hash, Ord)]
pub enum KnownNames {
    /// This is not a known name
    None,
    MiraiAbstractValue,
    MiraiAssume,
    MiraiAssumePreconditions,
    MiraiGetModelField,
    MiraiPostcondition,
    MiraiPreconditionStart,
    MiraiPrecondition,
    MiraiResult,
    MiraiSetModelField,
    MiraiShallowClone,
    MiraiVerify,
    StdFutureFromGenerator,
    StdIntrinsicsMulWithOverflow,
    StdIntrinsicsTransmute,
    StdOpsFunctionFnCall,
    StdOpsFunctionFnMutCallMut,
    StdOpsFunctionFnOnceCallOnce,
    StdPanickingBeginPanic,
    StdPanickingBeginPanicFmt,
    StdSliceLen,
    StdStrLen,
}

/// An analysis lifetime cache that contains a map from def ids to known names.
pub struct KnownNamesCache {
    name_cache: HashMap<DefId, KnownNames>,
}

type Iter<'a> = std::slice::Iter<'a, rustc::hir::map::DisambiguatedDefPathData>;

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
            |def_path_data_elem: Option<&rustc::hir::map::DisambiguatedDefPathData>| {
                match def_path_data_elem {
                    Some(ref elem) => match elem {
                        DisambiguatedDefPathData { data, .. } => match &data {
                            TypeNs(name) | ValueNs(name) => Some(*name),
                            _ => None,
                        },
                    },
                    None => None,
                }
            };

        // helper to get next elem from def path and return true if it is Impl path
        let path_data_elem_is_impl =
            |def_path_data_elem: Option<&rustc::hir::map::DisambiguatedDefPathData>| {
                if let Some(DisambiguatedDefPathData { data, .. }) = def_path_data_elem {
                    if let Impl = data {
                        true
                    } else {
                        false
                    }
                } else {
                    false
                }
            };

        let path_data_elem_as_disambiguator =
            |def_path_data_elem: Option<&rustc::hir::map::DisambiguatedDefPathData>| {
                if let Some(DisambiguatedDefPathData { disambiguator, .. }) = def_path_data_elem {
                    Some(*disambiguator)
                } else {
                    None
                }
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
            if let Some(1) = path_data_elem_as_disambiguator(def_path_data_iter.next()) {
                get_path_data_elem_name(def_path_data_iter.next())
                    .map(|n| match n.as_str().deref() {
                        "mul_with_overflow" => KnownNames::StdIntrinsicsMulWithOverflow,
                        "transmute" => KnownNames::StdIntrinsicsTransmute,
                        _ => KnownNames::None,
                    })
                    .unwrap_or(KnownNames::None)
            } else {
                KnownNames::None
            }
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
                    "begin_panic" | "panic" => KnownNames::StdPanickingBeginPanic,
                    "begin_panic_fmt" | "panic_fmt" => KnownNames::StdPanickingBeginPanicFmt,
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_slice_namespace = |mut def_path_data_iter: Iter<'_>| {
            if path_data_elem_is_impl(def_path_data_iter.next()) {
                get_path_data_elem_name(def_path_data_iter.next())
                    .map(|n| match n.as_str().deref() {
                        "len" => KnownNames::StdSliceLen,
                        _ => KnownNames::None,
                    })
                    .unwrap_or(KnownNames::None)
            } else {
                KnownNames::None
            }
        };

        let get_known_name_for_str_namespace = |mut def_path_data_iter: Iter<'_>| {
            if path_data_elem_is_impl(def_path_data_iter.next()) {
                get_path_data_elem_name(def_path_data_iter.next())
                    .map(|n| match n.as_str().deref() {
                        "len" => KnownNames::StdStrLen,
                        _ => KnownNames::None,
                    })
                    .unwrap_or(KnownNames::None)
            } else {
                KnownNames::None
            }
        };

        let get_known_name_for_known_crate = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str().deref() {
                    "future" => get_known_name_for_future_namespace(def_path_data_iter),
                    "intrinsics" => get_known_name_for_intrinsics_namespace(def_path_data_iter),
                    "ops" => get_known_name_for_ops_namespace(def_path_data_iter),
                    "panicking" => get_known_name_for_panicking_namespace(def_path_data_iter),
                    "slice" => get_known_name_for_slice_namespace(def_path_data_iter),
                    "str" => get_known_name_for_str_namespace(def_path_data_iter),
                    "mirai_abstract_value" => KnownNames::MiraiAbstractValue,
                    "mirai_assume" => KnownNames::MiraiAssume,
                    "mirai_assume_preconditions" => KnownNames::MiraiAssumePreconditions,
                    "mirai_get_model_field" => KnownNames::MiraiGetModelField,
                    "mirai_postcondition" => KnownNames::MiraiPostcondition,
                    "mirai_precondition_start" => KnownNames::MiraiPreconditionStart,
                    "mirai_precondition" => KnownNames::MiraiPrecondition,
                    "mirai_result" => KnownNames::MiraiResult,
                    "mirai_set_model_field" => KnownNames::MiraiSetModelField,
                    "mirai_shallow_clone" => KnownNames::MiraiShallowClone,
                    "mirai_verify" => KnownNames::MiraiVerify,
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let crate_name = tcx.crate_name(def_id.krate);
        match crate_name.as_str().deref() {
            "core" | "mirai_annotations" | "std" => {
                get_known_name_for_known_crate(def_path_data_iter)
            }
            _ => KnownNames::None,
        }
    }
}
