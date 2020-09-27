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
#![feature(box_patterns)]
#![feature(box_syntax)]
#![feature(core_intrinsics)]
#![feature(vec_remove_item)]

extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;

#[macro_use]
extern crate log;

/// If the currently analyzed function has been marked as angelic because was discovered
/// to do something that cannot be analyzed, or if the time taken to analyze the current
/// function exceeded k_limits::MAX_ANALYSIS_TIME_FOR_BODY, break out of the current loop.
/// When a timeout happens, currently analyzed function is marked as angelic.
macro_rules! check_for_early_break {
    ($sel:expr) => {
        if $sel.assume_function_is_angelic {
            break;
        }
        let elapsed_time_in_seconds = $sel.start_instant.elapsed().as_secs();
        if elapsed_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
            $sel.assume_function_is_angelic = true;
            break;
        }
    };
}

/// If the currently analyzed function has been marked as angelic because was discovered
/// to do something that cannot be analyzed, or if the time taken to analyze the current
/// function exceeded k_limits::MAX_ANALYSIS_TIME_FOR_BODY, return to the caller.
/// When a timeout happens, currently analyzed function is marked as angelic.
macro_rules! check_for_early_return {
    ($sel:expr) => {
        if $sel.assume_function_is_angelic {
            return;
        }
        let elapsed_time_in_seconds = $sel.start_instant.elapsed().as_secs();
        if elapsed_time_in_seconds >= k_limits::MAX_ANALYSIS_TIME_FOR_BODY {
            $sel.assume_function_is_angelic = true;
            return;
        }
    };
}

pub mod abstract_value;
pub mod block_visitor;
pub mod body_visitor;
pub mod bool_domain;
pub mod call_visitor;
pub mod callbacks;
pub mod constant_domain;
pub mod crate_visitor;
pub mod environment;
pub mod expected_errors;
pub mod expression;
pub mod fixed_point_visitor;
pub mod interval_domain;
pub mod k_limits;
pub mod known_names;
pub mod octagons_domain;
pub mod options;
pub mod path;
pub mod smt_solver;
pub mod summaries;
pub mod tag_domain;
pub mod type_visitor;
pub mod utils;
pub mod z3_solver;
