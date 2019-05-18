// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use log::debug;
use rustc::hir::def_id::DefId;
use rustc::hir::ItemKind;
use rustc::hir::Node;
use rustc::ty::subst::UnpackedKind;
use rustc::ty::{Ty, TyCtxt, TyKind};

/// Returns the location of the rust system binaries that are associated with this build of Mirai.
/// The location is obtained by looking at the contents of the environmental variables that were
/// set at the time Mirai was compiled. If the rust compiler was installed by rustup, the variables
/// RUSTUP_HOME and RUSTUP_TOOLCHAIN are used and these are set by the compiler itself.
/// If the rust compiler was compiled and installed in some other way, for example from a source
/// enlistment, then the RUST_SYSROOT variable must be set in the environment from which Mirai
/// is compiled.
pub fn find_sysroot() -> String {
    let home = option_env!("RUSTUP_HOME");
    let toolchain = option_env!("RUSTUP_TOOLCHAIN");
    match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .expect(
                "Could not find sysroot. Specify the RUST_SYSROOT environment variable, \
                 or use rustup to set the compiler to use for Mirai",
            )
            .to_owned(),
    }
}

/// Returns true if the function identified by def_id is a public function.
pub fn is_public(def_id: DefId, tcx: &TyCtxt<'_, '_, '_>) -> bool {
    if let Some(node) = tcx.hir().get_if_local(def_id) {
        match node {
            Node::Item(item) => {
                if let ItemKind::Fn(..) = item.node {
                    return item.vis.node.is_pub();
                }
                debug!("def_id is not a function item {:?}", item.node);
                return false;
            }
            Node::ImplItem(item) => {
                return item.vis.node.is_pub();
            }
            Node::TraitItem(..) => {
                return true;
            }
            _ => {
                debug!("def_id is not an item {:?}", node);
                return false;
            }
        }
    } else {
        debug!("def_id is not local {}", summary_key_str(tcx, def_id));
        false
    }
}

/// Returns a string that is a valid identifier, made up from the concatenation of
/// the string representationss of the given list of argument types.
pub fn argument_types_key_str<'tcx>(tcx: &TyCtxt<'_, '_, 'tcx>, ty: Ty<'tcx>) -> String {
    let mut result = "_".to_string();
    let bound_sig = ty.fn_sig(*tcx);
    let sig = bound_sig.skip_binder();
    for arg_ty in sig.inputs().iter() {
        result.push('_');
        append_mangled_type(&mut result, arg_ty, tcx);
    }
    result
}

/// Appends a string to str with the constraint that it must uniquely identify ty and also
/// be a valid identifier (so that core library contracts can be written for type specialized
/// generic trait methods).
fn append_mangled_type<'tcx>(str: &mut String, ty: Ty<'tcx>, tcx: &TyCtxt<'_, '_, 'tcx>) {
    use syntax::ast;
    use TyKind::*;
    match ty.sty {
        Bool => str.push_str("bool"),
        Char => str.push_str("char"),
        Int(int_ty) => {
            str.push_str(match int_ty {
                ast::IntTy::Isize => "isize",
                ast::IntTy::I8 => "i8",
                ast::IntTy::I16 => "i16",
                ast::IntTy::I32 => "i32",
                ast::IntTy::I64 => "i64",
                ast::IntTy::I128 => "i128",
            });
        }
        Uint(uint_ty) => {
            str.push_str(match uint_ty {
                ast::UintTy::Usize => "usize",
                ast::UintTy::U8 => "u8",
                ast::UintTy::U16 => "u16",
                ast::UintTy::U32 => "u32",
                ast::UintTy::U64 => "u64",
                ast::UintTy::U128 => "u128",
            });
        }
        Float(float_ty) => {
            str.push_str(match float_ty {
                ast::FloatTy::F32 => "f32",
                ast::FloatTy::F64 => "f64",
            });
        }
        Adt(def, subs) => {
            str.push_str(qualified_type_name(tcx, def.did).as_str());
            for sub in subs {
                if let UnpackedKind::Type(ty) = sub.unpack() {
                    str.push('_');
                    append_mangled_type(str, ty, tcx);
                }
            }
        }
        Foreign(def_id) => {
            str.push_str("extern_type_");
            str.push_str(qualified_type_name(tcx, def_id).as_str());
        }
        Str => str.push_str("str"),
        Array(ty, _) => {
            str.push_str("array_");
            append_mangled_type(str, ty, tcx);
        }
        Slice(ty) => {
            str.push_str("slice_");
            append_mangled_type(str, ty, tcx);
        }
        RawPtr(ty_and_mut) => {
            str.push_str("pointer_");
            match ty_and_mut.mutbl {
                rustc::hir::MutMutable => str.push_str("mut_"),
                rustc::hir::MutImmutable => str.push_str("const_"),
            }
            append_mangled_type(str, ty_and_mut.ty, tcx);
        }
        Ref(_, ty, mutability) => {
            str.push_str("ref_");
            if mutability == rustc::hir::MutMutable {
                str.push_str("mut_");
            }
            append_mangled_type(str, ty, tcx);
        }
        FnPtr(psig) => {
            str.push_str(&format!("FnPtr {:?}", psig));
        }
        Tuple(types) => {
            str.push_str("tuple_");
            str.push_str(&format!("{}", types.len()));
            types.iter().for_each(|t| {
                str.push('_');
                append_mangled_type(str, t.expect_ty(), tcx);
            });
        }
        Param(param_ty) => {
            let pty: Ty<'tcx> = param_ty.to_ty(*tcx);
            if ty.eq(pty) {
                str.push_str(&format!("{:?}", ty));
            } else {
                append_mangled_type(str, pty, tcx);
            }
        }
        _ => {
            //todo: add cases as the need arises, meanwhile make the need obvious.
            str.push_str(&format!("default formatted {:?}", ty))
        }
    }
}

/// Pretty much the same as summary_key_str but with _ used rather than . so that
/// the result can be appended to a valid identifier.
fn qualified_type_name(tcx: &TyCtxt<'_, '_, '_>, def_id: DefId) -> String {
    let mut name = if def_id.is_local() {
        tcx.crate_name.as_interned_str().as_str().to_string()
    } else {
        let cdata = tcx.crate_data_as_rc_any(def_id.krate);
        let cdata = cdata
            .downcast_ref::<rustc_metadata::cstore::CrateMetadata>()
            .unwrap();
        cdata.name.as_str().to_string()
    };
    for component in &tcx.def_path(def_id).data {
        name.push('_');
        name.push_str(component.data.as_interned_str().as_str().get());
        if component.disambiguator != 0 {
            name.push('_');
            let da = component.disambiguator.to_string();
            name.push_str(da.as_str());
        }
    }
    name
}

/// Constructs a string that uniquely identifies a definition to serve as a key to
/// the summary cache, which is a key value store. The string will always be the same as
/// long as the definition does not change its name or location, so it can be used to
/// transfer information from one compilation to the next, making incremental analysis possible.
pub fn summary_key_str(tcx: &TyCtxt<'_, '_, '_>, def_id: DefId) -> String {
    let mut name = if def_id.is_local() {
        tcx.crate_name.as_interned_str().as_str().to_string()
    } else {
        // This is both ugly and probably brittle, but I can't find any other
        // way to retrieve the crate name from a def_id that is not local.
        // tcx.crate_data_as_rc_any returns an untracked value, which is potentially problematic
        // as per the comments on the function:
        // "Note that this is *untracked* and should only be used within the query
        // system if the result is otherwise tracked through queries"
        // For now, this seems OK since we are only using the crate name.
        // Of course, should a crate name change in an incremental scenario this
        // is going to be the least of our worries.
        let cdata = tcx.crate_data_as_rc_any(def_id.krate);
        let cdata = cdata
            .downcast_ref::<rustc_metadata::cstore::CrateMetadata>()
            .unwrap();
        cdata.name.as_str().to_string()
    };
    for component in &tcx.def_path(def_id).data {
        if name.ends_with("foreign_contracts") {
            // By stripping off this special prefix, we allow this crate (or module) to define
            // functions that appear to be from other crates.
            // We use this to provide contracts for functions defined in crates we do not
            // wish to modify in place.
            name.clear();
        } else {
            name.push('.');
        }
        let component_name = component.data.as_interned_str().as_str();
        let component_name = component_name.get();
        if component_name == "{{impl}}" {
            name.push_str("implement");
        } else {
            name.push_str(component_name);
        }
        if component.disambiguator != 0 {
            name.push('_');
            let da = component.disambiguator.to_string();
            name.push_str(da.as_str());
        }
    }
    name
}
