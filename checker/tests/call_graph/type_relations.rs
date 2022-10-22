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

/* EXPECTED:DDLOGstart;
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
insert EdgeType(0,3);
insert EdgeType(1,8);
insert EdgeType(2,21);
insert EdgeType(3,25);
insert EqType(21,25);
insert EqType(21,27);
insert EqType(27,25);
insert EqType(29,28);
insert EqType(3,28);
insert EqType(3,29);
insert EqType(3,8);
insert EqType(8,28);
insert EqType(8,29);
insert Member(21,28);
insert Member(21,29);
insert Member(21,3);
insert Member(21,8);
insert Member(25,28);
insert Member(25,29);
insert Member(25,3);
insert Member(25,8);
insert Member(26,27);
insert Member(27,28);
insert Member(27,29);
insert Member(27,3);
insert Member(27,8);
commit;*/

/* EXPECTED:TYPEMAP{
  "3": "&Foo",
  "8": "&mut Foo",
  "21": "&[Foo]",
  "25": "std::vec::Vec<Foo>",
  "26": "Bar",
  "27": "[test::Foo]",
  "28": "test::Foo",
  "29": "Foo"
}*/

/* EXPECTED:CALL_SITES{
  "files": [
    "tests/call_graph/type_relations.rs",
    "/rustc/2287107588d92889d282e6cd3c1ca5df34cd34a5/library/core/src/fmt/mod.rs",
    "/rustc/2287107588d92889d282e6cd3c1ca5df34cd34a5/library/core/src/slice/mod.rs",
    "/rustc/2287107588d92889d282e6cd3c1ca5df34cd34a5/library/core/src/slice/iter/macros.rs",
    "/rustc/2287107588d92889d282e6cd3c1ca5df34cd34a5/library/alloc/src/vec/mod.rs",
    "/rustc/2287107588d92889d282e6cd3c1ca5df34cd34a5/library/std/src/io/stdio.rs",
    "/rustc/2287107588d92889d282e6cd3c1ca5df34cd34a5/library/alloc/src/boxed.rs",
    "/rustc/2287107588d92889d282e6cd3c1ca5df34cd34a5/library/core/src/ptr/mut_ptr.rs",
    "/rustc/2287107588d92889d282e6cd3c1ca5df34cd34a5/library/core/src/ptr/mod.rs",
    "/rustc/2287107588d92889d282e6cd3c1ca5df34cd34a5/library/alloc/src/slice.rs",
    "/rustc/2287107588d92889d282e6cd3c1ca5df34cd34a5/library/alloc/src/alloc.rs",
    "/rustc/2287107588d92889d282e6cd3c1ca5df34cd34a5/library/core/src/ptr/non_null.rs",
    "/rustc/2287107588d92889d282e6cd3c1ca5df34cd34a5/library/core/src/slice/iter.rs",
    "/rustc/2287107588d92889d282e6cd3c1ca5df34cd34a5/library/core/src/ptr/const_ptr.rs",
    "/rustc/2287107588d92889d282e6cd3c1ca5df34cd34a5/library/core/src/intrinsics.rs"
  ],
  "callables": [
    {
      "name": "type_relations.implement_type_relations_Foo.fmt",
      "file_index": 0,
      "first_line": 8,
      "local": true
    },
    {
      "name": "core.fmt.implement_core_fmt_Formatter.debug_struct_field1_finish",
      "file_index": 1,
      "first_line": 1977,
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
      "first_line": 322,
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
      "name": "core.slice.implement_slice_generic_par_T.iter",
      "file_index": 2,
      "first_line": 738,
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
      "first_line": 2916,
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
      "first_line": 2532,
      "local": true
    },
    {
      "name": "std.io.stdio._print",
      "file_index": 5,
      "first_line": 1029,
      "local": false
    },
    {
      "name": "core.fmt.implement_core_fmt_Arguments.new_v1",
      "file_index": 1,
      "first_line": 394,
      "local": false
    },
    {
      "name": "alloc.boxed.implement_alloc_boxed_Box_generic_par_T_generic_par_A.into_raw_with_allocator",
      "file_index": 6,
      "first_line": 1112,
      "local": true
    },
    {
      "name": "alloc.boxed.implement_alloc_boxed_Box_generic_par_T_generic_par_A.into_unique",
      "file_index": 6,
      "first_line": 1125,
      "local": true
    },
    {
      "name": "alloc.boxed.implement_alloc_boxed_Box_generic_par_T_generic_par_A.leak",
      "file_index": 6,
      "first_line": 1185,
      "local": true
    },
    {
      "name": "alloc.boxed.implement_alloc_boxed_Box_generic_par_T_generic_par_A.drop",
      "file_index": 6,
      "first_line": 1237,
      "local": true
    },
    {
      "name": "core.ptr.mut_ptr.implement_pointer_mut_generic_par_T.is_null",
      "file_index": 7,
      "first_line": 35,
      "local": true
    },
    {
      "name": "core.ptr.drop_in_place",
      "file_index": 8,
      "first_line": 487,
      "local": true
    },
    {
      "name": "alloc.slice.implement_slice_generic_par_T.into_vec",
      "file_index": 9,
      "first_line": 458,
      "local": true
    },
    {
      "name": "alloc.alloc.exchange_malloc",
      "file_index": 10,
      "first_line": 324,
      "local": false
    },
    {
      "name": "alloc.alloc.implement_alloc_alloc_Global.alloc_impl",
      "file_index": 10,
      "first_line": 172,
      "local": true
    },
    {
      "name": "core.ptr.non_null.implement_core_ptr_non_null_NonNull_generic_par_T.new",
      "file_index": 11,
      "first_line": 218,
      "local": true
    },
    {
      "name": "core.slice.iter.implement_core_slice_iter_Iter_generic_par_T.new",
      "file_index": 12,
      "first_line": 88,
      "local": true
    },
    {
      "name": "alloc.slice.hack.into_vec",
      "file_index": 9,
      "first_line": 97,
      "local": true
    },
    {
      "name": "alloc.vec.implement_alloc_vec_Vec_generic_par_T_generic_par_A.from_raw_parts_in",
      "file_index": 4,
      "first_line": 716,
      "local": true
    },
    {
      "name": "core.ptr.const_ptr.implement_pointer_const_generic_par_T.is_null",
      "file_index": 13,
      "first_line": 36,
      "local": true
    },
    {
      "name": "core.ptr.mut_ptr.implement_pointer_mut_generic_par_T.guaranteed_eq",
      "file_index": 7,
      "first_line": 721,
      "local": true
    },
    {
      "name": "core.intrinsics.foreign.ptr_guaranteed_cmp",
      "file_index": 14,
      "first_line": 2026,
      "local": false
    },
    {
      "name": "core.intrinsics.foreign.assert_inhabited",
      "file_index": 14,
      "first_line": 940,
      "local": false
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
      1113,
      31,
      14,
      15
    ],
    [
      6,
      1132,
      23,
      15,
      16
    ],
    [
      6,
      1133,
      5,
      15,
      17
    ],
    [
      4,
      2533,
      40,
      11,
      18
    ],
    [
      4,
      2921,
      62,
      9,
      18
    ],
    [
      4,
      2921,
      13,
      9,
      19
    ],
    [
      0,
      39,
      14,
      10,
      20
    ],
    [
      0,
      39,
      14,
      10,
      21
    ],
    [
      10,
      178,
      27,
      22,
      23
    ],
    [
      2,
      739,
      9,
      6,
      24
    ],
    [
      9,
      100,
      30,
      25,
      14
    ],
    [
      9,
      101,
      13,
      25,
      26
    ],
    [
      9,
      103,
      5,
      25,
      17
    ],
    [
      9,
      460,
      9,
      20,
      25
    ],
    [
      12,
      92,
      21,
      24,
      27
    ],
    [
      12,
      135,
      1,
      7,
      18
    ],
    [
      12,
      135,
      1,
      7,
      27
    ],
    [
      11,
      219,
      13,
      23,
      18
    ],
    [
      7,
      38,
      15,
      18,
      28
    ],
    [
      7,
      725,
      9,
      28,
      29
    ],
    [
      13,
      39,
      15,
      27,
      29
    ],
    [
      6,
      1131,
      30,
      15,
      30
    ]
  ]
}*/
