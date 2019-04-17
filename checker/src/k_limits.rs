// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
// Somewhat arbitrary constants used to limit things in the abstract interpreter that may
// take too long or use too much memory.

/// Helps to limit the size of summaries.
pub const MAX_INFERRED_PRECONDITIONS_DEFAULT: usize = 50;

/// Prevents the fixed point loop from creating ever more new abstract values of type Expression::Variable.
pub const MAX_PATH_LENGTH_DEFAULT: usize = 10;

/// The point at which diverging summaries experience exponential blowup right now.
pub const MAX_OUTER_FIXPOINT_ITERATIONS_DEFAULT: usize = 3;

/// The maximum number of seconds that MIRAI is willing to analyze a function body for.
pub const MAX_ANALYSIS_TIME_FOR_BODY_DEFAULT: u64 = 3;

#[derive(Debug, Clone)]
pub struct KLimitConfig {
    pub max_inferred_preconditions: usize,
    pub max_path_length: usize,
    pub max_outer_fixpoint_iterations: usize,
    pub max_analysis_time_for_body: u64,
}

impl KLimitConfig {
    pub fn new(
        max_inferred_preconditions: usize,
        max_path_length: usize,
        max_outer_fixpoint_iterations: usize,
        max_analysis_time_for_body: u64,
    ) -> KLimitConfig {
        KLimitConfig {
            max_inferred_preconditions,
            max_path_length,
            max_outer_fixpoint_iterations,
            max_analysis_time_for_body,
        }
    }
}

impl Default for KLimitConfig {
    fn default() -> Self {
        Self::new(
            self::MAX_INFERRED_PRECONDITIONS_DEFAULT,
            self::MAX_PATH_LENGTH_DEFAULT,
            self::MAX_OUTER_FIXPOINT_ITERATIONS_DEFAULT,
            self::MAX_ANALYSIS_TIME_FOR_BODY_DEFAULT,
        )
    }
}
