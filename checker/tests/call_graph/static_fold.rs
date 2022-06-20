// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Linear call graph with single type, no dominance, no loops.
// Includes call to println which is folded out.

fn fn1(x: u32) -> u32 {
    fn2(x)
}
fn fn2(x: u32) -> u32 {
    fn3(x)
}
fn fn3(x: u32) -> u32 {
    println!();
    x
}
pub fn main() {
    let x = 1;
    fn1(x);
}

/* CONFIG
{
    "reductions": ["Fold"],
    "included_crates": ["static_fold"],
    "datalog_config": {
        "datalog_backend": "DifferentialDatalog"
    }
}
*/

/* EXPECTED:DOT
digraph {
    0 [ label = "\"static_fold::main\"" ]
    1 [ label = "\"static_fold::fn1\"" ]
    2 [ label = "\"static_fold::fn2\"" ]
    3 [ label = "\"static_fold::fn3\"" ]
    0 -> 1 [ ]
    1 -> 2 [ ]
    2 -> 3 [ ]
}
*/

/* EXPECTED:DDLOG
start;
insert Edge(0,0,1);
insert Edge(1,1,2);
insert Edge(2,2,3);
insert EdgeType(0,0);
insert EdgeType(1,0);
insert EdgeType(2,0);
commit;
*/

/* EXPECTED:TYPEMAP
{
  "0": "u32"
}
*/

/* EXPECTED:CALL_SITES{
  "files": [
    "tests/call_graph/static_fold.rs",
    "/rustc/4c5f6e6277b89e47d73a192078697f7a5f3dc0ac/library/core/src/fmt/mod.rs"
  ],
  "callables": [
    [
      "static_fold.fn1",
      false
    ],
    [
      "static_fold.fn2",
      false
    ],
    [
      "static_fold.fn3",
      false
    ],
    [
      "static_fold.main",
      false
    ],
    [
      "std.io.stdio._print",
      true
    ],
    [
      "core.fmt.implement_core_fmt_Arguments.new_v1",
      false
    ]
  ],
  "calls": [
    [
      0,
      11,
      5,
      0,
      1
    ],
    [
      0,
      14,
      5,
      1,
      2
    ],
    [
      0,
      22,
      5,
      3,
      0
    ],
    [
      0,
      17,
      5,
      2,
      4
    ],
    [
      0,
      17,
      5,
      2,
      5
    ],
    [
      1,
      390,
      13,
      5,
      5
    ]
  ]
}*/
