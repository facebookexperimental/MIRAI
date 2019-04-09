// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// Somewhat arbitrary constants used to limit things in the abstract interpreter that may
// take too long or use too much memory.

/// The maximum number of seconds that MIRAI is willing to analyze a function body for.
pub const MAX_ANALYSIS_TIME_FOR_BODY: u64 = 3;

/// Helps to limit the size of summaries.
pub const MAX_INFERRED_PRECONDITIONS: usize = 50;

/// The point at which diverging summaries experience exponential blowup right now.
pub const MAX_OUTER_FIXPOINT_ITERATIONS: usize = 3;

/// Prevents the fixed point loop from creating ever more new abstract values of type Expression::Variable.
pub const MAX_PATH_LENGTH: usize = 10;

/// Refining values with a path condition that is a really big expression leads to exponential blow up.
pub const MAX_REFINE_DEPTH: usize = 9;
