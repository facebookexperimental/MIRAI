// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Linear call graph with function pointer calls, single type, dominance, and a loop.
// Using the Soufflé datalog backend.

fn fn1(x: u32, fn2: &fn(u32) -> u32, fn3: &fn(u32) -> u32) -> u32 {
    let y = fn2(x);
    fn3(y)
}
fn fn2(x: u32) -> u32 {
    x + 2
}
fn fn3(x: u32) -> u32 {
    fn4(x)
}
fn fn4(x: u32) -> u32 {
    if x > 1 {
        fn3(x - 1)
    } else {
        x
    }
}
pub fn main() {
    let x = 1;
    fn1(x, &(fn2 as fn(u32) -> u32), &(fn3 as fn(u32) -> u32));
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
    0 [ label = "\"fnptr_dom_loop_souffle::main\"" ]
    1 [ label = "\"fnptr_dom_loop_souffle::fn1\"" ]
    2 [ label = "\"fnptr_dom_loop_souffle::fn2\"" ]
    3 [ label = "\"fnptr_dom_loop_souffle::fn3\"" ]
    4 [ label = "\"fnptr_dom_loop_souffle::fn4\"" ]
    0 -> 1 [ ]
    0 -> 1 [ ]
    1 -> 2 [ ]
    1 -> 3 [ ]
    3 -> 4 [ ]
    4 -> 3 [ ]
}
*/

/* EXPECTED:SOUFFLE
2,30,0,1
1,0,1
2,1,2
3,1,3
4,3,4
5,4,30,0
1,1
2,0
3,0
4,0
5,0
*/

/* EXPECTED:TYPEMAP
{
  "0": "u32",
  "1": "&fn(u32) -> u32"
}
*/

/* EXPECTED:CALL_SITES{
  "files": [
    "tests/call_graph/fnptr_dom_loop_souffle.rs"
  ],
  "callables": [
    {
      "name": "/fnptr_dom_loop_souffle/fn1(u32,&ReLateBound(DebruijnIndex(0), BoundRegion { var: 0, kind: BrNamed(DefId(0:8 ~ fnptr_dom_loop_souffle[9ac1]::fn1::'_), '_) }) Binder(fn(u32) -> u32, []),&ReLateBound(DebruijnIndex(0), BoundRegion { var: 1, kind: BrNamed(DefId(0:9 ~ fnptr_dom_loop_souffle[9ac1]::fn1::'_#1), '_) }) Binder(fn(u32) -> u32, []))->u32",
      "file_index": 0,
      "first_line": 10,
      "local": true
    },
    {
      "name": "/fnptr_dom_loop_souffle/fn2(u32)->u32",
      "file_index": 0,
      "first_line": 14,
      "local": true
    },
    {
      "name": "/fnptr_dom_loop_souffle/fn3(u32)->u32",
      "file_index": 0,
      "first_line": 17,
      "local": true
    },
    {
      "name": "/fnptr_dom_loop_souffle/fn4(u32)->u32",
      "file_index": 0,
      "first_line": 20,
      "local": true
    },
    {
      "name": "/fnptr_dom_loop_souffle/main()->()",
      "file_index": 0,
      "first_line": 27,
      "local": true
    }
  ],
  "calls": [
    [
      0,
      11,
      13,
      0,
      1
    ],
    [
      0,
      12,
      5,
      0,
      2
    ],
    [
      0,
      18,
      5,
      2,
      3
    ],
    [
      0,
      22,
      9,
      3,
      2
    ],
    [
      0,
      29,
      5,
      4,
      0
    ]
  ]
}*/
