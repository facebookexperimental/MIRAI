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
insert EdgeType(1,6);
insert EdgeType(2,27);
insert EdgeType(3,45);
insert EqType(0,48);
insert EqType(0,49);
insert EqType(0,6);
insert EqType(27,45);
insert EqType(27,47);
insert EqType(47,45);
insert EqType(49,48);
insert EqType(6,48);
insert EqType(6,49);
insert Member(27,0);
insert Member(27,48);
insert Member(27,49);
insert Member(27,6);
insert Member(45,0);
insert Member(45,48);
insert Member(45,49);
insert Member(45,6);
insert Member(46,47);
insert Member(47,0);
insert Member(47,48);
insert Member(47,49);
insert Member(47,6);
commit;
*/

/* EXPECTED:TYPEMAP
{
  "0": "&Foo",
  "6": "&mut Foo",
  "27": "&[Foo]",
  "45": "std::vec::Vec<Foo>",
  "46": "Bar",
  "47": "[test::Foo]",
  "48": "test::Foo",
  "49": "Foo"
}
*/

/* EXPECTED:CALL_SITES{
  "files": [
    "tests/call_graph/type_relations.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/fmt/builders.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/fmt/mod.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/slice/mod.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/slice/iter/macros.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/alloc/src/vec/mod.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/std/src/io/stdio.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/mem/valid_align.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/num/nonzero.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/ptr/mod.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/ptr/metadata.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/ptr/const_ptr.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/ptr/mut_ptr.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/ptr/non_null.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/ptr/unique.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/intrinsics.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/result.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/convert/mod.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/slice/iter.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/mem/mod.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/slice/raw.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/alloc/layout.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/alloc/src/slice.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/alloc/src/alloc.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/alloc/src/raw_vec.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/alloc/src/boxed.rs",
    "/rustc/1fede1753c33f4ce0660ad9b8edbd618d9733daf/library/core/src/mem/manually_drop.rs"
  ],
  "callables": [
    {
      "name": "type_relations.implement.fmt",
      "file_index": 0,
      "first_line": 8,
      "local": true
    },
    {
      "name": "core.fmt.builders.implement_core_fmt_builders_DebugStruct.finish",
      "file_index": 1,
      "first_line": 233,
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
      "file_index": 2,
      "first_line": 317,
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
      "file_index": 3,
      "first_line": 734,
      "local": true
    },
    {
      "name": "core.slice.iter.implement_core_slice_iter_Iter_generic_par_T.next",
      "file_index": 4,
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
      "file_index": 5,
      "first_line": 2879,
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
      "file_index": 5,
      "first_line": 2496,
      "local": true
    },
    {
      "name": "std.io.stdio._print",
      "file_index": 6,
      "first_line": 1027,
      "local": false
    },
    {
      "name": "core.fmt.implement_core_fmt_Arguments.new_v1",
      "file_index": 2,
      "first_line": 388,
      "local": true
    },
    {
      "name": "core.mem.valid_align.implement.as_nonzero",
      "file_index": 7,
      "first_line": 37,
      "local": true
    },
    {
      "name": "core.num.nonzero.implement_core_num_nonzero_NonZeroUsize.new_unchecked",
      "file_index": 8,
      "first_line": 55,
      "local": false
    },
    {
      "name": "core.ptr.null",
      "file_index": 9,
      "first_line": 533,
      "local": true
    },
    {
      "name": "core.ptr.metadata.from_raw_parts",
      "file_index": 10,
      "first_line": 110,
      "local": true
    },
    {
      "name": "core.ptr.null_mut",
      "file_index": 9,
      "first_line": 710,
      "local": true
    },
    {
      "name": "core.ptr.metadata.from_raw_parts_mut",
      "file_index": 10,
      "first_line": 127,
      "local": true
    },
    {
      "name": "core.ptr.slice_from_raw_parts",
      "file_index": 9,
      "first_line": 737,
      "local": true
    },
    {
      "name": "core.ptr.const_ptr.implement.cast",
      "file_index": 11,
      "first_line": 46,
      "local": true
    },
    {
      "name": "core.ptr.slice_from_raw_parts_mut",
      "file_index": 9,
      "first_line": 769,
      "local": true
    },
    {
      "name": "core.ptr.mut_ptr.implement.cast",
      "file_index": 12,
      "first_line": 45,
      "local": true
    },
    {
      "name": "core.ptr.non_null.implement_core_ptr_non_null_NonNull_generic_par_T.new",
      "file_index": 13,
      "first_line": 218,
      "local": true
    },
    {
      "name": "core.ptr.mut_ptr.implement.is_null",
      "file_index": 12,
      "first_line": 35,
      "local": true
    },
    {
      "name": "core.ptr.non_null.implement_core_ptr_non_null_NonNull_generic_par_T.new_unchecked",
      "file_index": 13,
      "first_line": 196,
      "local": true
    },
    {
      "name": "core.ptr.non_null.implement_core_ptr_non_null_NonNull_slice_generic_par_T.slice_from_raw_parts",
      "file_index": 13,
      "first_line": 487,
      "local": true
    },
    {
      "name": "core.ptr.non_null.implement_core_ptr_non_null_NonNull_generic_par_T.as_ptr",
      "file_index": 13,
      "first_line": 330,
      "local": true
    },
    {
      "name": "core.ptr.non_null.implement_core_ptr_non_null_NonNull_slice_generic_par_T.as_non_null_ptr",
      "file_index": 13,
      "first_line": 532,
      "local": true
    },
    {
      "name": "core.ptr.mut_ptr.implement_pointer_mut_slice_generic_par_T.as_mut_ptr",
      "file_index": 12,
      "first_line": 1640,
      "local": true
    },
    {
      "name": "core.ptr.non_null.implement_core_ptr_non_null_NonNull_slice_generic_par_T.as_mut_ptr",
      "file_index": 13,
      "first_line": 552,
      "local": true
    },
    {
      "name": "core.ptr.unique.implement_core_ptr_unique_Unique_generic_par_T.new_unchecked",
      "file_index": 14,
      "first_line": 85,
      "local": true
    },
    {
      "name": "core.ptr.unique.implement_core_ptr_unique_Unique_generic_par_T.as_ptr",
      "file_index": 14,
      "first_line": 103,
      "local": true
    },
    {
      "name": "core.ptr.unique.implement_core_ptr_unique_Unique_generic_par_T.from",
      "file_index": 14,
      "first_line": 179,
      "local": true
    },
    {
      "name": "core.ptr.unique.implement_core_ptr_unique_Unique_generic_par_T.from",
      "file_index": 14,
      "first_line": 190,
      "local": true
    },
    {
      "name": "core.ptr.non_null.implement_core_ptr_non_null_NonNull_generic_par_T.from",
      "file_index": 13,
      "first_line": 784,
      "local": true
    },
    {
      "name": "core.ptr.const_ptr.implement.is_null",
      "file_index": 11,
      "first_line": 36,
      "local": true
    },
    {
      "name": "core.ptr.const_ptr.implement.guaranteed_eq",
      "file_index": 11,
      "first_line": 770,
      "local": true
    },
    {
      "name": "core.intrinsics.foreign_1.ptr_guaranteed_eq",
      "file_index": 15,
      "first_line": 1921,
      "local": false
    },
    {
      "name": "core.ptr.const_ptr.implement.add",
      "file_index": 11,
      "first_line": 863,
      "local": true
    },
    {
      "name": "core.ptr.const_ptr.implement.offset",
      "file_index": 11,
      "first_line": 450,
      "local": true
    },
    {
      "name": "core.ptr.const_ptr.implement.wrapping_add",
      "file_index": 11,
      "first_line": 1031,
      "local": true
    },
    {
      "name": "core.ptr.const_ptr.implement.wrapping_offset",
      "file_index": 11,
      "first_line": 532,
      "local": true
    },
    {
      "name": "core.ptr.mut_ptr.implement.guaranteed_eq",
      "file_index": 12,
      "first_line": 701,
      "local": true
    },
    {
      "name": "core.result.implement_core_result_Result_generic_par_T_generic_par_F.from_residual",
      "file_index": 16,
      "first_line": 2123,
      "local": true
    },
    {
      "name": "core.convert.implement_generic_par_T.from",
      "file_index": 17,
      "first_line": 559,
      "local": true
    },
    {
      "name": "core.fmt.implement_core_fmt_ArgumentV1.new",
      "file_index": 2,
      "first_line": 327,
      "local": true
    },
    {
      "name": "core.slice.iter.implement_core_slice_iter_Iter_generic_par_T.new",
      "file_index": 18,
      "first_line": 88,
      "local": true
    },
    {
      "name": "core.slice.implement.as_ptr",
      "file_index": 3,
      "first_line": 476,
      "local": true
    },
    {
      "name": "core.intrinsics.foreign_1.assume",
      "file_index": 15,
      "first_line": 749,
      "local": false
    },
    {
      "name": "core.mem.size_of",
      "file_index": 19,
      "first_line": 310,
      "local": true
    },
    {
      "name": "core.slice.iter.implement_core_slice_iter_Iter_generic_par_T.post_inc_start",
      "file_index": 4,
      "first_line": 85,
      "local": true
    },
    {
      "name": "core.ptr.mut_ptr.implement.offset",
      "file_index": 12,
      "first_line": 460,
      "local": true
    },
    {
      "name": "core.slice.raw.from_raw_parts",
      "file_index": 20,
      "first_line": 90,
      "local": true
    },
    {
      "name": "core.alloc.layout.implement.from_size_align_unchecked",
      "file_index": 21,
      "first_line": 98,
      "local": true
    },
    {
      "name": "core.mem.valid_align.implement.new_unchecked",
      "file_index": 7,
      "first_line": 28,
      "local": false
    },
    {
      "name": "core.alloc.layout.implement.dangling",
      "file_index": 21,
      "first_line": 194,
      "local": true
    },
    {
      "name": "core.ptr.invalid_mut",
      "file_index": 9,
      "first_line": 611,
      "local": true
    },
    {
      "name": "core.alloc.layout.implement.align",
      "file_index": 21,
      "first_line": 118,
      "local": false
    },
    {
      "name": "alloc.slice.implement.into_vec",
      "file_index": 22,
      "first_line": 526,
      "local": true
    },
    {
      "name": "alloc.alloc.exchange_malloc",
      "file_index": 23,
      "first_line": 318,
      "local": false
    },
    {
      "name": "alloc.raw_vec.implement_alloc_raw_vec_RawVec_generic_par_T_generic_par_A.from_raw_parts_in",
      "file_index": 24,
      "first_line": 215,
      "local": true
    },
    {
      "name": "alloc.raw_vec.implement_alloc_raw_vec_RawVec_generic_par_T_generic_par_A.ptr",
      "file_index": 24,
      "first_line": 223,
      "local": true
    },
    {
      "name": "alloc.alloc.alloc",
      "file_index": 23,
      "first_line": 88,
      "local": true
    },
    {
      "name": "core.alloc.layout.implement.size",
      "file_index": 21,
      "first_line": 108,
      "local": false
    },
    {
      "name": "alloc.alloc.alloc_zeroed",
      "file_index": 23,
      "first_line": 159,
      "local": true
    },
    {
      "name": "alloc.alloc.implement_alloc_alloc_Global.allocate",
      "file_index": 23,
      "first_line": 230,
      "local": true
    },
    {
      "name": "alloc.alloc.implement.alloc_impl",
      "file_index": 23,
      "first_line": 166,
      "local": false
    },
    {
      "name": "alloc.boxed.implement_alloc_boxed_Box_generic_par_T_generic_par_A.into_raw_with_allocator",
      "file_index": 25,
      "first_line": 1079,
      "local": true
    },
    {
      "name": "alloc.boxed.implement_alloc_boxed_Box_generic_par_T_generic_par_A.into_unique",
      "file_index": 25,
      "first_line": 1092,
      "local": true
    },
    {
      "name": "core.ptr.read",
      "file_index": 9,
      "first_line": 1134,
      "local": true
    },
    {
      "name": "alloc.boxed.implement_alloc_boxed_Box_generic_par_T_generic_par_A.leak",
      "file_index": 25,
      "first_line": 1152,
      "local": true
    },
    {
      "name": "alloc.boxed.implement_alloc_boxed_Box_generic_par_T_generic_par_A.drop",
      "file_index": 25,
      "first_line": 1179,
      "local": true
    },
    {
      "name": "core.mem.manually_drop.implement.new",
      "file_index": 26,
      "first_line": 70,
      "local": true
    },
    {
      "name": "core.mem.manually_drop.implement_core_mem_manually_drop_ManuallyDrop_generic_par_T.deref",
      "file_index": 26,
      "first_line": 153,
      "local": true
    },
    {
      "name": "alloc.slice.hack.into_vec",
      "file_index": 22,
      "first_line": 165,
      "local": true
    },
    {
      "name": "core.slice.implement.len",
      "file_index": 3,
      "first_line": 129,
      "local": true
    },
    {
      "name": "alloc.vec.implement_alloc_vec_Vec_generic_par_T_generic_par_A.from_raw_parts_in",
      "file_index": 5,
      "first_line": 690,
      "local": true
    },
    {
      "name": "alloc.vec.implement_alloc_vec_Vec_generic_par_T_generic_par_A.as_ptr",
      "file_index": 5,
      "first_line": 1137,
      "local": true
    },
    {
      "name": "alloc.vec.implement_alloc_vec_Vec_generic_par_T_generic_par_A.as_mut_ptr",
      "file_index": 5,
      "first_line": 1173,
      "local": true
    },
    {
      "name": "core.ptr.drop_in_place",
      "file_index": 9,
      "first_line": 486,
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
      7,
      39,
      18,
      14,
      15
    ],
    [
      9,
      534,
      5,
      16,
      17
    ],
    [
      9,
      711,
      5,
      18,
      19
    ],
    [
      9,
      738,
      5,
      20,
      17
    ],
    [
      9,
      738,
      20,
      20,
      21
    ],
    [
      9,
      770,
      5,
      22,
      19
    ],
    [
      9,
      770,
      24,
      22,
      23
    ],
    [
      13,
      219,
      13,
      24,
      25
    ],
    [
      13,
      221,
      27,
      24,
      26
    ],
    [
      13,
      489,
      18,
      27,
      26
    ],
    [
      13,
      489,
      38,
      27,
      22
    ],
    [
      13,
      489,
      70,
      27,
      28
    ],
    [
      13,
      534,
      18,
      29,
      26
    ],
    [
      13,
      534,
      41,
      29,
      28
    ],
    [
      13,
      534,
      41,
      29,
      30
    ],
    [
      13,
      553,
      9,
      31,
      29
    ],
    [
      13,
      553,
      9,
      31,
      28
    ],
    [
      14,
      87,
      36,
      32,
      26
    ],
    [
      14,
      104,
      9,
      33,
      28
    ],
    [
      14,
      180,
      9,
      34,
      35
    ],
    [
      14,
      180,
      20,
      34,
      36
    ],
    [
      11,
      39,
      9,
      37,
      38
    ],
    [
      11,
      39,
      43,
      37,
      16
    ],
    [
      11,
      774,
      9,
      38,
      39
    ],
    [
      11,
      868,
      18,
      40,
      41
    ],
    [
      11,
      1035,
      9,
      42,
      43
    ],
    [
      12,
      38,
      9,
      25,
      44
    ],
    [
      12,
      38,
      41,
      25,
      18
    ],
    [
      12,
      705,
      9,
      44,
      39
    ],
    [
      2,
      390,
      13,
      13,
      13
    ],
    [
      16,
      2125,
      27,
      45,
      46
    ],
    [
      2,
      339,
      5,
      3,
      47
    ],
    [
      3,
      735,
      9,
      6,
      48
    ],
    [
      18,
      89,
      19,
      48,
      49
    ],
    [
      18,
      92,
      13,
      48,
      50
    ],
    [
      18,
      92,
      21,
      48,
      37
    ],
    [
      18,
      94,
      26,
      48,
      51
    ],
    [
      18,
      95,
      17,
      48,
      42
    ],
    [
      18,
      97,
      17,
      48,
      40
    ],
    [
      18,
      100,
      25,
      48,
      26
    ],
    [
      18,
      135,
      1,
      7,
      28
    ],
    [
      18,
      135,
      1,
      7,
      52
    ],
    [
      18,
      135,
      1,
      52,
      43
    ],
    [
      18,
      135,
      1,
      52,
      51
    ],
    [
      18,
      135,
      1,
      52,
      28
    ],
    [
      18,
      135,
      1,
      52,
      28
    ],
    [
      18,
      135,
      1,
      52,
      26
    ],
    [
      18,
      135,
      1,
      52,
      28
    ],
    [
      18,
      135,
      1,
      52,
      53
    ],
    [
      18,
      135,
      1,
      7,
      50
    ],
    [
      18,
      135,
      1,
      7,
      28
    ],
    [
      18,
      135,
      1,
      7,
      25
    ],
    [
      18,
      135,
      1,
      7,
      51
    ],
    [
      18,
      135,
      1,
      7,
      50
    ],
    [
      18,
      135,
      1,
      7,
      37
    ],
    [
      20,
      97,
      11,
      54,
      20
    ],
    [
      21,
      100,
      40,
      55,
      56
    ],
    [
      21,
      196,
      18,
      57,
      26
    ],
    [
      21,
      196,
      41,
      57,
      58
    ],
    [
      21,
      196,
      71,
      57,
      59
    ],
    [
      0,
      39,
      14,
      10,
      60
    ],
    [
      0,
      39,
      14,
      10,
      61
    ],
    [
      24,
      216,
      30,
      62,
      32
    ],
    [
      24,
      224,
      9,
      63,
      33
    ],
    [
      23,
      89,
      27,
      64,
      65
    ],
    [
      23,
      89,
      42,
      64,
      59
    ],
    [
      23,
      160,
      34,
      66,
      65
    ],
    [
      23,
      160,
      49,
      66,
      59
    ],
    [
      23,
      231,
      9,
      67,
      68
    ],
    [
      25,
      1080,
      31,
      69,
      70
    ],
    [
      25,
      1081,
      10,
      69,
      33
    ],
    [
      25,
      1098,
      30,
      70,
      71
    ],
    [
      25,
      1099,
      10,
      70,
      34
    ],
    [
      25,
      1099,
      23,
      70,
      72
    ],
    [
      25,
      1100,
      5,
      70,
      73
    ],
    [
      25,
      1156,
      24,
      72,
      74
    ],
    [
      25,
      1156,
      24,
      72,
      75
    ],
    [
      25,
      1156,
      24,
      72,
      33
    ],
    [
      22,
      167,
      23,
      76,
      77
    ],
    [
      22,
      168,
      30,
      76,
      69
    ],
    [
      22,
      169,
      13,
      76,
      78
    ],
    [
      22,
      171,
      5,
      76,
      73
    ],
    [
      22,
      528,
      9,
      60,
      76
    ],
    [
      5,
      691,
      29,
      78,
      62
    ],
    [
      5,
      1140,
      19,
      79,
      63
    ],
    [
      5,
      1142,
      13,
      79,
      50
    ],
    [
      5,
      1142,
      21,
      79,
      25
    ],
    [
      5,
      1176,
      19,
      80,
      63
    ],
    [
      5,
      1178,
      13,
      80,
      50
    ],
    [
      5,
      1178,
      21,
      80,
      25
    ],
    [
      5,
      2497,
      18,
      11,
      54
    ],
    [
      5,
      2497,
      40,
      11,
      79
    ],
    [
      5,
      2884,
      13,
      9,
      81
    ],
    [
      5,
      2884,
      32,
      9,
      22
    ],
    [
      5,
      2884,
      62,
      9,
      80
    ]
  ]
}*/
