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
    "/rustc/2f2c438dce75d8cc532c3baa849eeddc0901802c/library/std/src/io/stdio.rs",
    "/rustc/2f2c438dce75d8cc532c3baa849eeddc0901802c/library/core/src/fmt/mod.rs",
    "/rustc/2f2c438dce75d8cc532c3baa849eeddc0901802c/library/core/src/slice/mod.rs",
    "/rustc/2f2c438dce75d8cc532c3baa849eeddc0901802c/library/core/src/ptr/metadata.rs"
  ],
  "callables": [
    {
      "name": "/static_fold/fn1(u32)->u32",
      "file_index": 0,
      "first_line": 10,
      "local": true
    },
    {
      "name": "/static_fold/fn2(u32)->u32",
      "file_index": 0,
      "first_line": 13,
      "local": true
    },
    {
      "name": "/static_fold/fn3(u32)->u32",
      "file_index": 0,
      "first_line": 16,
      "local": true
    },
    {
      "name": "/static_fold/main()->()",
      "file_index": 0,
      "first_line": 20,
      "local": true
    },
    {
      "name": "/std/std::io::_print(std::fmt::Arguments<'_>)->()",
      "file_index": 1,
      "first_line": 1094,
      "local": false
    },
    {
      "name": "/core/std::fmt::Arguments::<'a>::new_const(&'a [&'static str])->std::fmt::Arguments<'a>",
      "file_index": 2,
      "first_line": 297,
      "local": false
    },
    {
      "name": "/core/core::slice::<impl [T]>::len(&[T])->usize",
      "file_index": 3,
      "first_line": 140,
      "local": true
    },
    {
      "name": "/core/std::ptr::metadata(*const T)-><T as std::ptr::Pointee>::Metadata",
      "file_index": 4,
      "first_line": 94,
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
      3,
      141,
      9,
      6,
      7
    ]
  ]
}*/
