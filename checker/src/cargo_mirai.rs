// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// This provides an implementation for the "cargo mirai" subcommand.
// The mirai subcommand is the same as "cargo check" but with three differences:
// 1) It implicitly adds the options "--cfg mirai -Z always_encode_mir" to the rustc invocation.
// 2) It calls mirai rather than rustc for all the targets of the current package.
// 3) It runs cargo test --no-run for test targets.

use cargo_metadata::{Package, Target};
use std::ffi::OsString;
use std::ops::Index;
use std::path::Path;
use std::process::Command;

const CARGO_MIRAI_HELP: &str = r#"Static analysis tool for Rust programs

Usage:
    cargo mirai
"#;

pub fn main() {
    if std::env::args().any(|a| a == "--help" || a == "-h") {
        println!("{CARGO_MIRAI_HELP}");
        return;
    }
    if std::env::args().any(|a| a == "--version" || a == "-V") {
        let version_info = rustc_tools_util::get_version_info!();
        println!("{version_info}");
        return;
    }

    match std::env::args().nth(1).as_ref().map(AsRef::<str>::as_ref) {
        Some(s) if s.ends_with("mirai") || s.ends_with("mirai.exe") => {
            // Get here for the top level cargo execution, i.e. "cargo mirai".
            call_cargo();
        }
        Some(s) if s.ends_with("rustc") || s.ends_with("rustc.exe") => {
            // 'cargo rustc ..' redirects here because RUSTC_WRAPPER points to this binary.
            // execute rustc with MIRAI applicable parameters for dependencies and call MIRAI
            // to analyze targets in the current package.
            call_rustc_or_mirai();
        }
        Some(arg) => {
            eprintln!(
                "`cargo-mirai` called with invalid first argument: {arg}; please only invoke this binary through `cargo mirai`" 
            );
        }
        _ => {
            eprintln!(
                "`cargo-mirai` called without first argument; please only invoke this binary through `cargo mirai`"
            );
        }
    }
}

/// Read the toml associated with the current directory and
/// recursively execute cargo for each applicable package target/workspace member in the toml
fn call_cargo() {
    let manifest_path =
        get_arg_flag_value("--manifest-path").map(|m| Path::new(&m).canonicalize().unwrap());

    let mut cmd = cargo_metadata::MetadataCommand::new();
    if let Some(ref manifest_path) = manifest_path {
        cmd.manifest_path(manifest_path);
    }

    let metadata = if let Ok(metadata) = cmd.exec() {
        metadata
    } else {
        eprintln!("Could not obtain Cargo metadata; likely an ill-formed manifest");
        std::process::exit(1);
    };

    if let Some(root) = metadata.root_package() {
        call_cargo_on_each_package_target(root);
        return;
    }

    // There is no root, this must be a workspace, so call_cargo_on_each_package_target on each workspace member
    for package_id in &metadata.workspace_members {
        let package = metadata.index(package_id);
        call_cargo_on_each_package_target(package);
    }
}

fn call_cargo_on_each_package_target(package: &Package) {
    let lib_only = get_arg_flag_presence("--lib");
    for target in &package.targets {
        let kind = target
            .kind
            .get(0)
            .expect("bad cargo metadata: target::kind");
        if lib_only && kind != "lib" {
            continue;
        }
        call_cargo_on_target(target, kind);
    }
}

fn call_cargo_on_target(target: &Target, kind: &str) {
    // Build a cargo command for target
    let mut cmd =
        Command::new(std::env::var_os("CARGO").unwrap_or_else(|| OsString::from("cargo")));
    match kind {
        "bin" => {
            cmd.arg("check");
            cmd.arg("--bin").arg(&target.name);
        }
        "lib" => {
            cmd.arg("check");
            cmd.arg("--lib");
        }
        "test" => {
            cmd.arg("test");
            cmd.arg("--test").arg(&target.name);
            cmd.arg("--no-run");
        }
        _ => {
            return;
        }
    }

    let mut args = std::env::args().skip(2);
    // Add cargo args to cmd until first `--`.
    for arg in args.by_ref() {
        if arg == "--" {
            break;
        }
        if arg == "--lib" {
            continue;
        }
        cmd.arg(arg);
    }

    // Serialize the remaining args into an environment variable.
    let args_vec: Vec<String> = args.collect();
    if !args_vec.is_empty() {
        cmd.env(
            "MIRAI_FLAGS",
            serde_json::to_string(&args_vec).expect("failed to serialize args"),
        );
    }

    // Force cargo to recompile all dependencies with MIRAI friendly flags
    cmd.env("RUSTFLAGS", "--cfg mirai -Z always_encode_mir");

    // Replace the rustc executable through RUSTC_WRAPPER environment variable so that rustc
    // calls generated by cargo come back to cargo-mirai.
    let path = std::env::current_exe().expect("current executable path invalid");
    cmd.env("RUSTC_WRAPPER", path);

    // Communicate the name of the root crate to the calls to cargo-mirai that are invoked via
    // the RUSTC_WRAPPER setting.
    cmd.env("MIRAI_CRATE", target.name.replace('-', "_"));

    // Communicate the target kind of the root crate to the calls to cargo-mirai that are invoked via
    // the RUSTC_WRAPPER setting.
    cmd.env("MIRAI_KIND", kind);

    // Set the tool chain to be compatible with mirai
    if let Some(toolchain) = option_env!("RUSTUP_TOOLCHAIN") {
        cmd.env("RUSTUP_TOOLCHAIN", toolchain);
    }

    // Execute cmd
    let exit_status = cmd
        .spawn()
        .expect("could not run cargo")
        .wait()
        .expect("failed to wait for cargo");

    if !exit_status.success() {
        std::process::exit(exit_status.code().unwrap_or(-1))
    }
}

fn call_rustc_or_mirai() {
    if let Some(crate_name) = get_arg_flag_value("--crate-name") {
        if let Ok(mirai_crate) = std::env::var("MIRAI_CRATE") {
            if crate_name.eq(&mirai_crate) {
                if let Ok(kind) = std::env::var("MIRAI_KIND") {
                    if let Some(t) = get_arg_flag_value("--crate-type") {
                        if kind.eq(&t) {
                            call_mirai();
                            return;
                        }
                    }
                    if get_arg_flag_value("--test").is_some() {
                        call_mirai();
                        return;
                    }
                }
                return;
            }
        }
    }
    if get_arg_flag_value("--test").is_none() {
        call_rustc();
    }
}

fn call_mirai() {
    let mut path = std::env::current_exe().expect("current executable path invalid");
    let extension = path.extension().map(|e| e.to_owned());
    path.pop(); // remove the cargo_mirai bit
    path.push("mirai");
    if let Some(ext) = extension {
        path.set_extension(ext);
    }
    let mut cmd = Command::new(path);
    cmd.args(std::env::args().skip(2));
    let exit_status = cmd
        .spawn()
        .expect("could not run mirai")
        .wait()
        .expect("failed to wait for mirai");

    if !exit_status.success() {
        std::process::exit(exit_status.code().unwrap_or(-1))
    }
}

fn call_rustc() {
    // todo: invoke the rust compiler for the appropriate tool chain?
    let mut cmd =
        Command::new(std::env::var_os("RUSTC").unwrap_or_else(|| OsString::from("rustc")));
    cmd.args(std::env::args().skip(2));
    let exit_status = cmd
        .spawn()
        .expect("could not run rustc")
        .wait()
        .expect("failed to wait for rustc");

    if !exit_status.success() {
        std::process::exit(exit_status.code().unwrap_or(-1))
    }
}

// `--name` is present
fn get_arg_flag_presence(name: &str) -> bool {
    let mut args = std::env::args().take_while(|val| val != "--");
    loop {
        let arg = match args.next() {
            Some(arg) => arg,
            None => return false,
        };
        if arg.starts_with(name) {
            return true;
        }
    }
}

// `--name value` or `--name=value`
fn get_arg_flag_value(name: &str) -> Option<String> {
    let mut args = std::env::args().take_while(|val| val != "--");
    loop {
        let arg = match args.next() {
            Some(arg) => arg,
            None => return None,
        };
        if !arg.starts_with(name) {
            continue;
        }
        // Strip `name`.
        let suffix = &arg[name.len()..];
        if suffix.is_empty() {
            // This argument is `name` and the next one is the value.
            return args.next();
        } else if let Some(arg_value) = suffix.strip_prefix('=') {
            return Some(arg_value.to_owned());
        }
    }
}
