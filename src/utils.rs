// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use rustc::hir::def_id::DefId;
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
