// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// Somewhat arbitrary constants used to limit things in the abstract interpreter that may
// take too long or use too much memory.

/// Prevents the fixed point loop from creating ever more new abstract values of type Expression::Variable.
pub const MAX_PATH_LENGTH: usize = 10;

/// The point at which diverging summaries experience exponential blowup right now.
pub const MAX_OUTER_FIXPOINT_ITERATIONS: usize = 3;
