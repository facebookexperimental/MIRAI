// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Test case that ensures that if a static call is made without
// any arguments, an edge *is* added to the call graph.

fn fn1() -> u32 {
    1
}
pub fn main() {
    fn1();
}

/* CONFIG
{
    "reductions": [],
    "included_crates": [],
    "datalog_config": {
        "datalog_backend": "DifferentialDatalog"
    }
}
*/

/* EXPECTED:DOT
digraph {
    0 [ label = "\"static_no_args::main\"" ]
    1 [ label = "\"static_no_args::fn1\"" ]
    0 -> 1 [ ]
}
*/

/* EXPECTED:DDLOG
start;
insert Edge(0,0,1);
insert EdgeType(0,0);
commit;
*/

/* EXPECTED:TYPEMAP
{
  "0": ""
}
*/

/* EXPECTED:CALL_SITES
{
  "files": [
    "tests/call_graph/static_no_args.rs"
  ],
  "callables": [
    [
      "static_no_args.main",
      false
    ],
    [
      "static_no_args.fn1",
      false
    ]
  ],
  "calls": [
    [
      0,
      14,
      5,
      0,
      1
    ]
  ]
}
*/
