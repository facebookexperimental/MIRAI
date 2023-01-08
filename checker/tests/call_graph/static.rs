// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Linear call graph with static calls, single type, no dominance, no loops.

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
        "datalog_backend": "DifferentialDatalog"
    }
}
*/

/* EXPECTED:DOT
digraph {
    0 [ label = "\"static::main\"" ]
    1 [ label = "\"static::fn1\"" ]
    2 [ label = "\"static::fn2\"" ]
    3 [ label = "\"static::fn3\"" ]
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
    "tests/call_graph/static.rs"
  ],
  "callables": [
    {
      "name": "/static/fn1(u32)->u32",
      "file_index": 0,
      "first_line": 9,
      "local": true
    },
    {
      "name": "/static/fn2(u32)->u32",
      "file_index": 0,
      "first_line": 12,
      "local": true
    },
    {
      "name": "/static/fn3(u32)->u32",
      "file_index": 0,
      "first_line": 15,
      "local": true
    },
    {
      "name": "/static/main()->()",
      "file_index": 0,
      "first_line": 18,
      "local": true
    }
  ],
  "calls": [
    [
      0,
      10,
      5,
      0,
      1
    ],
    [
      0,
      13,
      5,
      1,
      2
    ],
    [
      0,
      20,
      5,
      3,
      0
    ]
  ]
}*/
