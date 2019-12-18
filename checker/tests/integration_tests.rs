// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//
// In an ideal world there would be a stable well documented set of crates containing a specific
// version of the Rust compiler along with its sources and debug information. We'd then just get
// those from crate.io and merely go on our way as just another Rust application. Rust compiler
// upgrades will be non events for Mirai until it is ready to jump to another release and old
// versions of Mirai will continue to work just as before.
//
// In the current world, however, we have to use the following hacky feature to get access to a
// private and not very stable set of APIs from whatever compiler is in the path when we run Mirai.
// While pretty bad, it is a lot less bad than having to write our own compiler, so here goes.
#![feature(rustc_private)]
#![feature(box_syntax)]
#![feature(vec_remove_item)]

extern crate mirai;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_rayon;
extern crate syntax;
extern crate tempdir;

use mirai::callbacks;
use mirai::options::{DiagLevel, Options};
use mirai::utils;
use regex::Regex;
use rustc_rayon::iter::IntoParallelIterator;
use rustc_rayon::iter::ParallelIterator;
use std::fs;
use std::fs::read_to_string;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use tempdir::TempDir;
use walkdir::WalkDir;

// Run the tests in the tests/run-pass directory.
// Eventually, there will be separate test cases for other directories such as compile-fail.
#[test]
fn run_pass() {
    let extern_deps = vec![
        (
            "mirai_annotations",
            find_extern_library("mirai_annotations"),
        ),
        ("contracts", find_extern_library("contracts")),
    ];
    let mut run_pass_path = PathBuf::from_str("tests/run-pass").unwrap();
    if !run_pass_path.exists() {
        run_pass_path = PathBuf::from_str("checker/tests/run-pass").unwrap();
    }
    assert_eq!(run_directory(run_pass_path, extern_deps), 0);
}

fn find_extern_library(base_name: &str) -> String {
    let mut deps_path = PathBuf::from_str("../target/debug").unwrap();
    if !deps_path.exists() {
        deps_path = PathBuf::from_str("target/debug").unwrap();
    }

    for entry in WalkDir::new(deps_path)
        .contents_first(true)
        .into_iter()
        .filter_map(|e| e.ok())
    {
        if !entry.file_type().is_file() {
            continue;
        };
        let file_name = entry.file_name().to_str().unwrap_or("");
        // On Windows we have either lib{base_name}.rlib or {base_name}.dll. We match any form.
        if !file_name.starts_with(format!("lib{}", base_name).as_str())
            && !file_name.starts_with(base_name)
        {
            continue;
        }
        if entry.path().to_str().unwrap().contains(".dSYM/") {
            // There might be a directory .dSYM which contains the same library file
            // but for different purpose. Skip this.
            continue;
        }
        if !file_name.ends_with(".rlib")
            && !file_name.ends_with(".dylib")
            && !file_name.ends_with(".so")
            && !file_name.ends_with(".dll")
        {
            continue;
        }
        println!("resolving {}", entry.path().to_str().unwrap());
        return entry.path().to_str().unwrap().to_string();
    }
    unreachable!("could not find the `{}` library", base_name);
}

// Iterates through the files in the directory at the given path and runs each as a separate test
// case. For each case, a temporary output directory is created. The cases are then iterated in
// parallel and run via invoke_driver.
fn run_directory(directory_path: PathBuf, extern_deps: Vec<(&str, String)>) -> usize {
    let sys_root = utils::find_sysroot();
    let mut files_and_temp_dirs = Vec::new();
    for entry in fs::read_dir(directory_path).expect("failed to read run-pass dir") {
        let entry = entry.unwrap();
        if !entry.file_type().unwrap().is_file() {
            continue;
        };
        let file_path = entry.path();
        let file_name = entry.file_name();
        let temp_dir = TempDir::new("miraiTest").expect("failed to create a temp dir");
        let temp_dir_path_buf = temp_dir.into_path();
        let output_dir_path_buf = temp_dir_path_buf.join(file_name.into_string().unwrap());
        fs::create_dir(output_dir_path_buf.as_path()).expect("failed to create test output dir");
        files_and_temp_dirs.push((
            file_path.into_os_string().into_string().unwrap(),
            output_dir_path_buf.into_os_string().into_string().unwrap(),
        ));
    }
    if cfg!(target_os = "linux") {
        files_and_temp_dirs
            .into_iter()
            .fold(0, |acc, (file_name, temp_dir_path)| {
                acc + self::invoke_driver(
                    file_name,
                    temp_dir_path,
                    sys_root.clone(),
                    extern_deps.clone(),
                )
            })
    } else {
        files_and_temp_dirs
            .into_par_iter()
            .fold(
                || 0,
                |acc, (file_name, temp_dir_path)| {
                    acc + self::invoke_driver(
                        file_name,
                        temp_dir_path,
                        sys_root.clone(),
                        extern_deps.clone(),
                    )
                },
            )
            .reduce(|| 0, |acc, code| acc + code)
    }
}

// Runs the single test case found in file_name, using temp_dir_path as the place
// to put compiler output, which for Mirai includes the persistent summary store.
fn invoke_driver(
    file_name: String,
    temp_dir_path: String,
    sys_root: String,
    extern_deps: Vec<(&str, String)>,
) -> usize {
    // Read MIRAI options from file content.
    let mut options = Options::default();
    options.diag_level = DiagLevel::PARANOID;
    let mut rustc_args = vec![]; // any arguments after `--` for rustc
    {
        let file_content = read_to_string(&Path::new(&file_name)).unwrap();
        let options_re = Regex::new(r"(?m)^\s*//\s*MIRAI_FLAGS\s(?P<flags>.*)$").unwrap();
        if let Some(captures) = options_re.captures(&file_content) {
            rustc_args = options.parse_from_str(&captures["flags"]);
        }
    }

    // Setup rustc call.
    let mut command_line_arguments: Vec<String> = vec![
        String::from("--crate-name mirai"),
        file_name.clone(),
        String::from("--crate-type"),
        String::from("lib"),
        String::from("--edition=2018"),
        String::from("-C"),
        String::from("debuginfo=2"),
        String::from("--out-dir"),
        temp_dir_path,
        String::from("--sysroot"),
        sys_root,
        String::from("-Z"),
        String::from("span_free_formats"),
        String::from("-Z"),
        String::from("mir-emit-retag"),
    ];
    command_line_arguments.extend(rustc_args);
    if options.test_only {
        // #[test] will be ignored unless we enable this.
        command_line_arguments.push("--test".to_string());
    }
    for extern_dep in extern_deps {
        command_line_arguments.push("--extern".to_string());
        command_line_arguments.push(format!("{}={}", extern_dep.0, extern_dep.1));
    }

    let mut call_backs = callbacks::MiraiCallbacks::test_runner(options);
    let result = std::panic::catch_unwind(move || {
        rustc_driver::run_compiler(
            &command_line_arguments,
            &mut call_backs,
            None, // use default file loader
            None, // emit output to default destination
        )
    });
    match result {
        Ok(_) => 0,
        Err(_) => {
            println!("{} failed", file_name);
            1
        }
    }
}
