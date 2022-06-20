// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Linear call graph with function pointer calls, single type, no dominance, no loops.
// Taking a slice of the call graph from fn1.

fn fn1(x: u32, fn2: &fn(u32) -> u32) -> u32 {
    fn2(x)
}
fn fn2(x: u32) -> u32 {
    fn3(x)
}
fn fn3(x: u32) -> u32 {
    x
}
pub fn main() {
    let x = 1;
    fn1(x, &(fn2 as fn(u32) -> u32));
}

/* CONFIG
{
    "reductions": [{"Slice": "fn1"}],
    "included_crates": [],
    "datalog_config": {
        "datalog_backend": "DifferentialDatalog"
    }
}
*/

/* EXPECTED:DOT
digraph {
    0 [ label = "\"fnptr_slice::fn1\"" ]
    1 [ label = "\"fnptr_slice::fn2\"" ]
    2 [ label = "\"fnptr_slice::fn3\"" ]
    0 -> 1 [ ]
    1 -> 2 [ ]
}
*/

/* EXPECTED:DDLOG
start;
insert Edge(0,0,1);
insert Edge(1,1,2);
insert EdgeType(0,0);
insert EdgeType(1,0);
commit;
*/

/* EXPECTED:TYPEMAP
{
  "0": "u32"
}
*/

/* EXPECTED:CALL_SITES{
  "files": [
    "tests/call_graph/fnptr_slice.rs"
  ],
  "callables": [
    [
      "fnptr_slice.fn1",
      false
    ],
    [
      "fnptr_slice.fn2",
      false
    ],
    [
      "fnptr_slice.fn3",
      false
    ],
    [
      "fnptr_slice.main",
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
      21,
      5,
      3,
      0
    ]
  ]
}*/
