# Why plug into the Rust compiler

A compiler that is written from the ground up to support incremental static analysis is by far the best starting point
for a static analysis project.

The Rust compiler is admirable in many ways, but it is not particularly well suited as a platform for static analysis.
It is, however, the only game in town and writing another compiler will be a huge effort in exchange for little
economic gain. It will also be a loser's game until the core language stops evolving and there is a well written
standard defining exactly what Rust is.

Even then, an analysis project starting from scratch is at the disadvantage that a huge amount of work needs to be done
before any results become apparent. Plugging into the existing Rust compiler makes it easier to start testing and
iterating designs from day one.

The real alternative to writing the analyzer as a Rust compiler plug in, is to write it as a consumer of the compiler's
output: [LLVM bitcode](https://www.llvm.org/docs/BitCodeFormat.html). This approach has the considerable advantage
that one can use the LLVM infrastructure during the analysis. Moreover, link time optimization provides a stage where
the analyzer can get access to code other than Rust code.

This approach has already been explored and is described [here](https://soarlab.org/papers/2018_atva_bhr.pdf). That
project does not seem active at the moment.

Despite the potential, the LLVM approach also has a big disadvantage: The connection between the code seen by the
analyzer and the code seen by a Rust programmer, becomes very distant and some aspects become completely disconnected.
For example, when low level routines copy a structure by means of a byte string copy, the impact this has on the
heap model of a calling function becomes hard/impossible to model in a summary of the low level routine.

Another problem is with calls made to functions via polymorphic pointers. At the Rust compiler level, an analyzer can
gather sufficient call site information to statically resolve (de-virtualize) such calls, which is good for precision.
At the LLVM level, the connection with the Rust types has been lost, and it becomes considerably more challenging to
do static resolution.

Right now, it seems that the approach followed by MIRAI, namely to plug into the Rust compiler, has been, and still is,
the best approach available.

