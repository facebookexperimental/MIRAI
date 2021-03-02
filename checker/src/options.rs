// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use clap::{App, AppSettings, Arg, Error, ErrorKind};
use itertools::Itertools;
use mirai_annotations::*;
use rustc_session::config::ErrorOutputType;
use rustc_session::early_error;

/// Creates the clap::App metadata for argument parsing.
fn make_options_parser<'a>() -> App<'a, 'a> {
    // We could put this into lazy_static! with a Mutex around, but we really do not expect
    // to construct this more then once per regular program run.
    App::new("MIRAI")
    .setting(AppSettings::NoBinaryName)
    .version("v1.0.5")
    .arg(Arg::with_name("single_func")
        .long("single_func")
        .takes_value(true)
        .help("Focus analysis on the named function.")
        .long_help("Name is the simple name of a top-level crate function or a MIRAI summary key."))
    .arg(Arg::with_name("test_only")
        .long("test_only")
        .short("t")
        .takes_value(false)
        .help("Focus analysis on #[test] methods.")
        .long_help("Only #[test] methods and their usage are analyzed. This must be used together with the rustc --test option.")) //todo: just set the --test option, dammit
    .arg(Arg::with_name("diag")
        .long("diag")
        .possible_values(&["relaxed", "strict", "paranoid"])
        .default_value("relaxed")
        .help("Level of diagnostics.\n")
        .long_help("With `relaxed`, false positives will be avoided where possible.\nWith 'strict' optimistic assumptions are made about unanalyzable calls.\nWith `paranoid`, all errors will be reported.\n"))
    .arg(Arg::with_name("constant_time")
        .long("constant_time")
        .takes_value(true)
        .help("Enable verification of constant-time security.")
        .long_help("Name is a top-level crate type"))
}

/// Represents options passed to MIRAI.
#[derive(Debug, Default)]
pub struct Options {
    pub single_func: Option<String>,
    pub test_only: bool,
    pub diag_level: DiagLevel,
    pub constant_time_tag_name: Option<String>,
}

/// Represents diag level.
#[derive(Debug, PartialEq, PartialOrd)]
pub enum DiagLevel {
    /// When a function can't be fully analyzed, for example because it calls a function
    /// without a body and no foreign function summary, it is simply assumed to be correct (angelic).
    /// This is transitive: calling an angelic function causes the caller to become angelic itself.
    /// This minimizes false positives but can lead to a lot code not being analyzed
    /// while devirtualization isn't perfect and not all intrinsics have been modeled.
    Relaxed,
    /// Always emit at least one diagnostic for functions that cannot be fully analyzed because of
    /// time-outs or calls to functions without bodies or foreign function summaries. In this mode
    /// the analysis is sound because every potential issue in analyzed has a related diagnostic,
    /// but it is also angelic because it assumes that argument values provided by code that is not
    /// being analyzed will never cause the program to wrong, i.e. that non analyzed code is "angelic".
    Strict,
    /// Like strict, but issues diagnostics if non analyzed code can provide arguments will cause
    /// the analyzed code to go wrong. I.e. it requires all preconditions to be explicit.
    /// This mode should be used for any library whose callers are not known and there not analyzed.
    Paranoid,
}

impl Default for DiagLevel {
    fn default() -> Self {
        DiagLevel::Relaxed
    }
}

impl Options {
    /// Parse options from an argument string. The argument string will be split using unix
    /// shell escaping rules. Any content beyond the leftmost `--` token will be returned
    /// (excluding this token).
    pub fn parse_from_str(&mut self, s: &str) -> Vec<String> {
        self.parse(&shellwords::split(s).unwrap_or_else(|e| {
            early_error(
                ErrorOutputType::default(),
                &format!("Cannot parse argument string: {:?}", e),
            )
        }))
    }

    /// Parses options from a list of strings. Any content beyond the leftmost `--` token
    /// will be returned (excluding this token).
    pub fn parse(&mut self, args: &[String]) -> Vec<String> {
        let mut mirai_args_end = args.len();
        let mut rustc_args_start = 0;
        if let Some((p, _)) = args.iter().find_position(|s| s.as_str() == "--") {
            mirai_args_end = p;
            rustc_args_start = p + 1;
        }
        let mirai_args = &args[0..mirai_args_end];
        let matches = if rustc_args_start == 0 {
            // The arguments may not be intended for MIRAI and may get here
            // via some tool, so do not report errors here, but just assume
            // that the arguments were not meant for MIRAI.
            match make_options_parser().get_matches_from_safe(mirai_args.iter()) {
                Ok(matches) => {
                    // Looks like these are MIRAI options after all and there are no rustc options.
                    rustc_args_start = args.len();
                    matches
                }
                Err(Error {
                    kind: ErrorKind::HelpDisplayed,
                    message,
                    ..
                }) => {
                    // help is ambiguous, so display both MIRAI and rustc help.
                    println!("{}\n", message);
                    return args.to_vec();
                }
                Err(..) => {
                    // Just send all of the arguments to rustc.
                    // Note that this means that MIRAI options and rustc options must always
                    // be separated by --. I.e. any MIRAI options present in arguments list
                    // will stay unknown to MIRAI and will make rustc unhappy.
                    return args.to_vec();
                }
            }
        } else {
            // This will display error diagnostics for arguments that are not valid for MIRAI.
            make_options_parser().get_matches_from(mirai_args.iter())
        };

        if matches.is_present("single_func") {
            self.single_func = matches.value_of("single_func").map(|s| s.to_string());
        }
        if matches.is_present("test_only") {
            self.test_only = true;
        }
        if matches.is_present("diag") {
            self.diag_level = match matches.value_of("diag").unwrap() {
                "relaxed" => DiagLevel::Relaxed,
                "strict" => DiagLevel::Strict,
                "paranoid" => DiagLevel::Paranoid,
                _ => assume_unreachable!(),
            };
        }
        if matches.is_present("constant_time") {
            self.constant_time_tag_name = matches.value_of("constant_time").map(|s| s.to_owned());
        }
        args[rustc_args_start..].to_vec()
    }
}
