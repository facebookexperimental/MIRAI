# Why use MIR?

MIRAI analyzes the [Mid-level Intermediate Representation](https://rustc-dev-guide.rust-lang.org/mir/index.html)
produced by the Rust compiler in preparation for code generation.

Possible alternatives would be to use higher level representations such as 
the [AST](https://rustc-dev-guide.rust-lang.org/syntax-intro.html), 
the [High-Level Intermediate Representation](https://rustc-dev-guide.rust-lang.org/hir.html) or the
[Typed High-Level Intermediate Representation](https://rustc-dev-guide.rust-lang.org/thir.html).

All of these approaches would require some form of lowering in order to perform an analysis of the execution of the
project of interest. This would provide flexibility and more control, but it also involves a substantial amount
of largely duplicated work 
([see also](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/WhyPlugIn.md)).

There is another consideration: Unlike the AST, HIR and THIR, MIR is
serialized into the compiler output for dependencies. Since MIRAI does a top-down analysis 
([see also](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/WhyTopDown.md)), the convenience
and performance benefit of not re-compiling every dependency, are factors of overriding importance.