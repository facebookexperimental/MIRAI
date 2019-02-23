// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use rustc::hir::def_id::DefId;
use rustc::hir::ItemKind;
use rustc::hir::Node;
use rustc::ty::TyCtxt;
use rustc_target::spec::abi::Abi;

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

/// Returns true if the function identified by def_id is a Rust intrinsic function.
/// Warning: it is not clear what will happen if def_id does not identify a function.
pub fn is_rust_intrinsic(def_id: DefId, tcx: &TyCtxt) -> bool {
    let binder = tcx.fn_sig(def_id);
    let sig = binder.skip_binder();
    match sig.abi {
        Abi::RustIntrinsic => true,
        _ => false,
    }
}

/// Returns true if the function identified by def_id is a public function.
pub fn is_public(def_id: DefId, tcx: &TyCtxt) -> bool {
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

/// Constructs a string that uniquely identifies a definition to serve as a key to
/// the summary cache, which is a key value store. The string will always be the same as
/// long as the definition does not change its name or location, so it can be used to
/// transfer information from one compilation to the next, making incremental analysis possible.
pub fn summary_key_str(tcx: &TyCtxt, def_id: DefId) -> String {
    let crate_name = if def_id.is_local() {
        tcx.crate_name.as_interned_str().as_str().get()
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
        cdata.name.as_str().get()
    };
    let mut name = String::from(crate_name);
    for component in &tcx.def_path(def_id).data {
        name.push('.');
        let cn = component.data.as_interned_str().as_str().get();
        name.push_str(cn);
        if component.disambiguator != 0 {
            name.push(':');
            let da = component.disambiguator.to_string();
            name.push_str(da.as_str());
        }
    }
    name
}
