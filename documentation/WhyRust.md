# Why Rust?

Rust is not an easy language. It can be hard for programmers that are used to automatic memory management to learn how 
to deal with the life times in the type system. The language semantics are complicated and not formally defined. There
is only one implementation of the language and the code of this implementation is not well commented. Moreover, the
language and its implementation are still evolving rapidly.

Other aspects of the language are also very hard for a static analyzer to deal with, such as unsafe code, transmutation, 
generics, traits and higher order functions. And, of course, calling assembly/C/C++ code from Rust programs is a vital
feature of the language.

All of this adds up to gigantic challenge for any effort to build a verifier for Rust. It is certainly no easier than
doing so for C++, perhaps even harder.

Furthermore, Rust is still a nascent language and the commercial incentive to develop a verifier for Rust
is very small at best.

Finally, the Rust type system, the linter, the standard library and the Rust ecosystem, together conspire to make
the corpus of Rust code much less error-prone than most other languages, and especially C/C++. Consequently, the
value that a static analyzer adds to the Rust ecosystem is much less than the value such an analyzer would add to
the C++ ecosystem.

So why target Rust?

If verification is the goal, you probably should focus on a constrained subset of the language and target small programs 
written to make verification possible. Much can be learned from doing this, and I applaud such efforts.

For better or for worse, however, MIRAI was commissioned in order to analyze a 
large [code base](https://github.com/diem/diem) that enthusiastically makes use of every feature of Rust.

As always, the large size of the Diem code base, the small size of the development team, and the tight time window of
the target market, made it impossible for developers to fully embrace and enable verification.

The focus of MIRAI thus soon shifted from verification to bug finding. The challenge is to analyze code that has not
been annotated or constrained and to do so in a reasonable time and with reasonably few false positives.

The design decisions of MIRAI should be understood in this context.

That said, MIRAI is a capable analyzer and can do well when verification of small programs written in a constrained
subset of Rust is the goal. There is, of course, ample room for improvement. That would have to wait for a V2 effort
and that would have to wait for a time when the necessary resources become available.