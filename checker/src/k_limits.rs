// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// Somewhat arbitrary constants used to limit things in the abstract interpreter that may
// take too long or use too much memory.

/// The maximum number of seconds that MIRAI is willing to analyze a function body for.
pub const MAX_ANALYSIS_TIME_FOR_BODY: u64 = 70;

/// The maximum number of elements in a byte array that will be individually tracked.
pub const MAX_BYTE_ARRAY_LENGTH: usize = 100;

/// Helps to limit the size of summaries.
pub const MAX_INFERRED_PRECONDITIONS: usize = 50;

/// If Expressions get too large they become too costly to refine.
pub const MAX_EXPRESSION_SIZE: u64 = 1_000;

/// Double the observed maximum used in practice.
pub const MAX_FIXPOINT_ITERATIONS: usize = 10;

/// Prevents the outer fixed point loop from creating ever more new abstract values of type Expression::Variable.
pub const MAX_PATH_LENGTH: usize = 30;

/// Refining values with a path condition that is a really deep expression leads to exponential blow up.
pub const MAX_REFINE_DEPTH: usize = 40;
