# Architecture

Mirai is a plugin for the Rust compiler. It comes into play after type analysis is done and the IR has been lowered
into MIR.

In order to make the Rust compiler aware of Mirai, we provide our own compiler main routine in src/main.rs and then use
a private API to provide the compiler with a customized collection of call backs functions that will be called as needed.
See src/callbacks.rs. We then get Cargo to invoke our main routine as if if were the normal Rust compiler.

The analysis performed by Mirai is modular and incremental. Each function is analyzed in a separate context and perhaps 
in parallel with other functions. Information is exchanged via a shared in memory key-value store database that holds a 
summary for each function.

The analyzer is an abstract interpreter over the MIR control flow graph. The state of the interpreter is stored in a
functional data structure so that every edge in the control flow graph can have a state associated with it. Instructions
that can cause problems are flagged during interpretation. Once interpretation has reached a fixed point, the paths that
can reach problematic instructions are either turned into error messages or are used to add preconditions to the
function (if it is not public).

Function summaries are in-lined and specialized at call sites.




