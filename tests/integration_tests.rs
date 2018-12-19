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

extern crate mirai;
extern crate rustc_driver;
extern crate rustc_rayon;
extern crate tempdir;

use mirai::callbacks;
use mirai::utils;
use rustc_rayon::iter::IntoParallelIterator;
use rustc_rayon::iter::ParallelIterator;
use std::fs;
use std::path::PathBuf;
use std::str::FromStr;

use tempdir::TempDir;

// Run the tests in the tests/run-pass directory.
// Eventually, there will be separate test cases for other directories such as compile-fail.
#[test]
fn run_pass() {
    let run_pass_path = PathBuf::from_str("tests/run-pass").unwrap();
    run_directory(run_pass_path);
}

// Iterates through the files in the directory at the given path and runs each as a separate test
// case. For each case, a temporary output directory is created. The cases are then iterated in
// parallel and run via invoke_driver.
fn run_directory(directory_path: PathBuf) {
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
    files_and_temp_dirs
        .into_par_iter()
        .for_each(|(file_name, temp_dir_path)| {
            self::invoke_driver(file_name, temp_dir_path, sys_root.clone());
        });
}

// Runs the single test case found in file_name, using temp_dir_path as the place
// to put compiler output, which for Mirai includes the persistent summary store.
fn invoke_driver(file_name: String, temp_dir_path: String, sys_root: String) {
    rustc_driver::run(|| {
        let command_line_arguments: Vec<String> = vec![
            String::from("--crate-name mirai"),
            file_name,
            String::from("--crate-type"),
            String::from("lib"),
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
            String::from("-Z"),
            String::from("mir-opt-level=0"),
        ];

        rustc_driver::run_compiler(
            &command_line_arguments,
            box callbacks::MiraiCallbacks::default(),
            None, // use default file loader
            None, // emit output to default destination
        )
    });
}
