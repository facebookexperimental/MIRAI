// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Linear call graph with static calls, single type, no dominance, no loops.
// Using the Soufflé datalog backend.

fn fn1(x: u32) -> u32 {
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
    fn1(x);
}

/* CONFIG
{
    "reductions": [],
    "included_crates": [],
    "datalog_config": {
        "datalog_backend": "Souffle"
    }
}
*/

/* EXPECTED:DOT
digraph {
    0 [ label = "\"static_souffle::main\"" ]
    1 [ label = "\"static_souffle::fn1\"" ]
    2 [ label = "\"static_souffle::fn2\"" ]
    3 [ label = "\"static_souffle::fn3\"" ]
    0 -> 1 [ ]
    1 -> 2 [ ]
    2 -> 3 [ ]
}
*/

/* EXPECTED:SOUFFLE
0,0,1
1,1,2
2,2,30,0
1,0
2,0
*/

/* EXPECTED:TYPEMAP
{
  "0": "u32"
}
*/

/* EXPECTED:CALL_SITES{
  "files": [
    "tests/call_graph/static_souffle.rs"
  ],
  "callables": [
    {
      "name": "/static_souffle/fn1(u32)->u32",
      "file_index": 0,
      "first_line": 10,
      "local": true
    },
    {
      "name": "/static_souffle/fn2(u32)->u32",
      "file_index": 0,
      "first_line": 13,
      "local": true
    },
    {
      "name": "/static_souffle/fn3(u32)->u32",
      "file_index": 0,
      "first_line": 16,
      "local": true
    },
    {
      "name": "/static_souffle/main()->()",
      "file_index": 0,
      "first_line": 19,
      "local": true
    }
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
