// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//
// Testing derivation of type relations with heuristics.

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Foo {
    x: u32,
}

fn foo_ref(f: &Foo) {
    println!("{}", f.x);
}

fn foo_mut_ref(f: &mut Foo) {
    f.x = 0;
    println!("{}", f.x);
}

fn foo_slice_iter(fs: &[Foo]) {
    for f in fs.iter() {
        println!("{}", f.x);
    }
}

fn foo_vec_iter(fs: Vec<Foo>) {
    for f in fs.iter() {
        println!("{}", f.x);
    }
}

pub fn main() {
    let mut f1 = Foo { x: 1 };
    foo_ref(&f1);
    foo_mut_ref(&mut f1);

    let f2 = vec![Foo { x: 0 }, Foo { x: 1 }];
    foo_slice_iter(&f2);
    foo_vec_iter(f2);
}

/* CONFIG
{
    "reductions": ["Fold", "Clean"],
    "included_crates": [
        "type_relations"
    ],
    "datalog_config": {
        "datalog_backend": "DifferentialDatalog",
        "type_relations_path": "tests/call_graph/type_relations.json"
    }
}
*/

/* EXPECTED:DOT
digraph {
    0 [ label = "\"type_relations::main\"" ]
    1 [ label = "\"type_relations::foo_ref\"" ]
    2 [ label = "\"type_relations::foo_mut_ref\"" ]
    3 [ label = "\"type_relations::foo_slice_iter\"" ]
    4 [ label = "\"type_relations::foo_vec_iter\"" ]
    0 -> 1 [ ]
    0 -> 2 [ ]
    0 -> 3 [ ]
    0 -> 4 [ ]
}
*/

/* EXPECTED:DDLOG
start;
insert Dom(1,2);
insert Dom(1,3);
insert Dom(1,4);
insert Dom(2,3);
insert Dom(2,4);
insert Dom(3,4);
insert Edge(0,0,1);
insert Edge(1,0,2);
insert Edge(2,0,3);
insert Edge(3,0,4);
insert EdgeType(0,0);
insert EdgeType(1,5);
insert EdgeType(2,19);
insert EdgeType(3,22);
insert EqType(0,25);
insert EqType(0,26);
insert EqType(0,5);
insert EqType(19,22);
insert EqType(19,24);
insert EqType(24,22);
insert EqType(26,25);
insert EqType(5,25);
insert EqType(5,26);
insert Member(19,0);
insert Member(19,25);
insert Member(19,26);
insert Member(19,5);
insert Member(22,0);
insert Member(22,25);
insert Member(22,26);
insert Member(22,5);
insert Member(23,24);
insert Member(24,0);
insert Member(24,25);
insert Member(24,26);
insert Member(24,5);
commit;
*/

/* EXPECTED:TYPEMAP
{
  "0": "&Foo",
  "5": "&mut Foo",
  "19": "&[Foo]",
  "22": "std::vec::Vec<Foo>",
  "23": "Bar",
  "24": "[test::Foo]",
  "25": "test::Foo",
  "26": "Foo"
}
*/

/* EXPECTED:CALL_SITES{
  "files": [
    "tests/call_graph/type_relations.rs",
    "/rustc/7665c3543079ebc3710b676d0fd6951bedfd4b29/library/core/src/fmt/mod.rs",
    "/rustc/7665c3543079ebc3710b676d0fd6951bedfd4b29/library/core/src/slice/mod.rs",
    "/rustc/7665c3543079ebc3710b676d0fd6951bedfd4b29/library/core/src/slice/iter/macros.rs",
    "/rustc/7665c3543079ebc3710b676d0fd6951bedfd4b29/library/alloc/src/vec/mod.rs",
    "/rustc/7665c3543079ebc3710b676d0fd6951bedfd4b29/library/std/src/io/stdio.rs",
    "/rustc/7665c3543079ebc3710b676d0fd6951bedfd4b29/library/alloc/src/boxed.rs",
    "/rustc/7665c3543079ebc3710b676d0fd6951bedfd4b29/library/core/src/intrinsics.rs",
    "/rustc/7665c3543079ebc3710b676d0fd6951bedfd4b29/library/core/src/slice/iter.rs",
    "/rustc/7665c3543079ebc3710b676d0fd6951bedfd4b29/library/core/src/ptr/non_null.rs",
    "/rustc/7665c3543079ebc3710b676d0fd6951bedfd4b29/library/alloc/src/alloc.rs",
    "/rustc/7665c3543079ebc3710b676d0fd6951bedfd4b29/library/core/src/convert/mod.rs",
    "/rustc/7665c3543079ebc3710b676d0fd6951bedfd4b29/library/alloc/src/slice.rs",
    "/rustc/7665c3543079ebc3710b676d0fd6951bedfd4b29/library/core/src/ptr/mod.rs"
  ],
  "callables": [
    {
      "name": "type_relations.implement.fmt",
      "file_index": 0,
      "first_line": 8,
      "local": true
    },
    {
      "name": "core.fmt.implement_core_fmt_Formatter.debug_struct_field1_finish",
      "file_index": 1,
      "first_line": 1972,
      "local": false
    },
    {
      "name": "type_relations.foo_ref",
      "file_index": 0,
      "first_line": 13,
      "local": true
    },
    {
      "name": "core.fmt.implement_core_fmt_ArgumentV1.new_display",
      "file_index": 1,
      "first_line": 318,
      "local": true
    },
    {
      "name": "type_relations.foo_mut_ref",
      "file_index": 0,
      "first_line": 17,
      "local": true
    },
    {
      "name": "type_relations.foo_slice_iter",
      "file_index": 0,
      "first_line": 22,
      "local": true
    },
    {
      "name": "core.slice.implement.iter",
      "file_index": 2,
      "first_line": 734,
      "local": true
    },
    {
      "name": "core.slice.iter.implement_core_slice_iter_Iter_generic_par_T.next",
      "file_index": 3,
      "first_line": 134,
      "local": true
    },
    {
      "name": "type_relations.foo_vec_iter",
      "file_index": 0,
      "first_line": 28,
      "local": true
    },
    {
      "name": "alloc.vec.implement_alloc_vec_Vec_generic_par_T_generic_par_A.drop",
      "file_index": 4,
      "first_line": 2915,
      "local": true
    },
    {
      "name": "type_relations.main",
      "file_index": 0,
      "first_line": 34,
      "local": true
    },
    {
      "name": "alloc.vec.implement_alloc_vec_Vec_generic_par_T_generic_par_A.deref",
      "file_index": 4,
      "first_line": 2531,
      "local": true
    },
    {
      "name": "std.io.stdio._print",
      "file_index": 5,
      "first_line": 1026,
      "local": false
    },
    {
      "name": "core.fmt.implement_core_fmt_Arguments.new_v1",
      "file_index": 1,
      "first_line": 390,
      "local": true
    },
    {
      "name": "alloc.boxed.implement_alloc_boxed_Box_generic_par_T_generic_par_A.into_unique",
      "file_index": 6,
      "first_line": 1119,
      "local": true
    },
    {
      "name": "core.intrinsics.foreign_1.assert_inhabited",
      "file_index": 7,
      "first_line": 1168,
      "local": false
    },
    {
      "name": "core.slice.iter.implement_core_slice_iter_Iter_generic_par_T.new",
      "file_index": 8,
      "first_line": 88,
      "local": true
    },
    {
      "name": "core.intrinsics.foreign_1.ptr_guaranteed_eq",
      "file_index": 7,
      "first_line": 2233,
      "local": false
    },
    {
      "name": "core.ptr.non_null.implement_core_ptr_non_null_NonNull_generic_par_T.new",
      "file_index": 9,
      "first_line": 218,
      "local": true
    },
    {
      "name": "alloc.vec.implement_alloc_vec_Vec_generic_par_T_generic_par_A.as_ptr",
      "file_index": 4,
      "first_line": 1167,
      "local": true
    },
    {
      "name": "alloc.vec.implement_alloc_vec_Vec_generic_par_T_generic_par_A.as_mut_ptr",
      "file_index": 4,
      "first_line": 1204,
      "local": true
    },
    {
      "name": "alloc.alloc.implement.alloc_impl",
      "file_index": 10,
      "first_line": 166,
      "local": true
    },
    {
      "name": "core.convert.implement_generic_par_T.from",
      "file_index": 11,
      "first_line": 559,
      "local": true
    },
    {
      "name": "core.intrinsics.foreign_1.assume",
      "file_index": 7,
      "first_line": 1062,
      "local": false
    },
    {
      "name": "alloc.slice.implement.into_vec",
      "file_index": 12,
      "first_line": 528,
      "local": true
    },
    {
      "name": "alloc.alloc.exchange_malloc",
      "file_index": 10,
      "first_line": 318,
      "local": false
    },
    {
      "name": "alloc.boxed.implement_alloc_boxed_Box_generic_par_T_generic_par_A.into_raw_with_allocator",
      "file_index": 6,
      "first_line": 1106,
      "local": true
    },
    {
      "name": "alloc.boxed.implement_alloc_boxed_Box_generic_par_T_generic_par_A.leak",
      "file_index": 6,
      "first_line": 1179,
      "local": true
    },
    {
      "name": "alloc.boxed.implement_alloc_boxed_Box_generic_par_T_generic_par_A.drop",
      "file_index": 6,
      "first_line": 1231,
      "local": true
    },
    {
      "name": "alloc.slice.hack.into_vec",
      "file_index": 12,
      "first_line": 167,
      "local": true
    },
    {
      "name": "alloc.vec.implement_alloc_vec_Vec_generic_par_T_generic_par_A.from_raw_parts_in",
      "file_index": 4,
      "first_line": 716,
      "local": true
    },
    {
      "name": "core.ptr.drop_in_place",
      "file_index": 13,
      "first_line": 487,
      "local": true
    }
  ],
  "calls": [
    [
      0,
      8,
      10,
      0,
      1
    ],
    [
      0,
      14,
      5,
      2,
      3
    ],
    [
      0,
      19,
      5,
      4,
      3
    ],
    [
      0,
      23,
      14,
      5,
      6
    ],
    [
      0,
      23,
      14,
      5,
      7
    ],
    [
      0,
      24,
      9,
      5,
      3
    ],
    [
      0,
      29,
      14,
      8,
      6
    ],
    [
      0,
      29,
      14,
      8,
      7
    ],
    [
      0,
      30,
      9,
      8,
      3
    ],
    [
      0,
      32,
      1,
      8,
      9
    ],
    [
      0,
      36,
      5,
      10,
      2
    ],
    [
      0,
      37,
      5,
      10,
      4
    ],
    [
      0,
      40,
      5,
      10,
      5
    ],
    [
      0,
      40,
      20,
      10,
      11
    ],
    [
      0,
      41,
      5,
      10,
      8
    ],
    [
      0,
      42,
      1,
      10,
      9
    ],
    [
      0,
      14,
      5,
      2,
      12
    ],
    [
      0,
      19,
      5,
      4,
      12
    ],
    [
      0,
      24,
      9,
      5,
      12
    ],
    [
      0,
      30,
      9,
      8,
      12
    ],
    [
      0,
      14,
      5,
      2,
      13
    ],
    [
      0,
      19,
      5,
      4,
      13
    ],
    [
      0,
      24,
      9,
      5,
      13
    ],
    [
      0,
      30,
      9,
      8,
      13
    ],
    [
      6,
      1125,
      30,
      14,
      15
    ],
    [
      8,
      92,
      21,
      16,
      17
    ],
    [
      8,
      135,
      1,
      7,
      17
    ],
    [
      9,
      219,
      13,
      18,
      17
    ],
    [
      4,
      1172,
      21,
      19,
      17
    ],
    [
      8,
      135,
      1,
      7,
      17
    ],
    [
      4,
      1209,
      21,
      20,
      17
    ],
    [
      1,
      392,
      13,
      13,
      13
    ],
    [
      10,
      172,
      27,
      21,
      22
    ],
    [
      2,
      735,
      9,
      6,
      16
    ],
    [
      8,
      92,
      13,
      16,
      23
    ],
    [
      8,
      135,
      1,
      7,
      23
    ],
    [
      8,
      135,
      1,
      7,
      23
    ],
    [
      0,
      39,
      14,
      10,
      24
    ],
    [
      0,
      39,
      14,
      10,
      25
    ],
    [
      10,
      172,
      27,
      21,
      18
    ],
    [
      6,
      1107,
      31,
      26,
      14
    ],
    [
      6,
      1126,
      23,
      14,
      27
    ],
    [
      6,
      1127,
      5,
      14,
      28
    ],
    [
      12,
      170,
      30,
      29,
      26
    ],
    [
      12,
      171,
      13,
      29,
      30
    ],
    [
      12,
      173,
      5,
      29,
      28
    ],
    [
      12,
      530,
      9,
      24,
      29
    ],
    [
      4,
      1172,
      13,
      19,
      23
    ],
    [
      4,
      1209,
      13,
      20,
      23
    ],
    [
      4,
      2532,
      40,
      11,
      19
    ],
    [
      4,
      2920,
      13,
      9,
      31
    ],
    [
      4,
      2920,
      62,
      9,
      20
    ]
  ]
}*/
