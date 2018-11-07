# Rust static analysis/verification reading and resources


## Rust analysis

* Implementing taint analysis and software fault isolation for Rust 
using the [SMACK tool](https://www.ics.uci.edu/~aburtsev/doc/crust-hotos17.pdf).
* Another paper about Rust verification with SMACK: http://soarlab.org/publications/atva2018-bhr.pdf
* Documentation on MIR, the Rust intermediate representation where borrow checking and optimization passes 
happen: https://rust-lang-nursery.github.io/rustc-guide/mir/index.html
* A tool for visualizing MIRI, among other things: https://play.rust-lang.org/
* MIRI: MIR interpreter: https://github.com/solson/miri.
* A tutorial on creating a drop-in replacement for rustc: https://github.com/nrc/stupid-stats
* HIR: An IR between the AST and MIR: https://rust-lang-nursery.github.io/rustc-guide/hir.html
* Clippy, the AST-based Rust linter: https://github.com/rust-lang-nursery/rust-clippy
* Plugins for fetching the source code for a Rust crate (important for building/analyzing third-party crates)
    * https://github.com/rust-lang/cargo/issues/1861
    * https://github.com/JanLikar/cargo-clone

## Rust semantic foundations

* Rustbelt—proving that unsafe code in the Rust libraries is safe w.r.t safe Rust, and laying the foundations for 
others to prove that their unsafe code has the same properties. Section 2 is also a good intro of Rust for the 
PL-oriented reader: https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf
* Rust distilled: focusing on a formalization of Rust source instead of MIR (they contend that Rustbelt is really about
MIR): https://arxiv.org/abs/1806.02693
* This blog post by Ralf (one of the Rustbelt authors) attempts to express the Rust borrow checker as a dynamic 
analysis. It's the best explanation of the borrow checker I've seen and a promising start toward ensuring safe 
interaction between safe and unsafe Rust: https://www.ralfj.de/blog/2018/08/07/stacked-borrows.html. Lots of other 
good posts under there too.

## Other

* Rust verification gitter channel: https://gitter.im/rust-lang/wg-verification.
* Crate with Z3 bindings for Rust: https://crates.io/crates/z3

