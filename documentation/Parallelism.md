# Parallelism

It is always tempting to try and use every core on the processor to speed up static analysis. On the face of it, quite
a lot can be done in parallel, since units of abstraction such as functions are often independent of each other and
can be analyzed without any knowledge of each other.

The rust compiler, however, exposes and enables very little of this potential parallelism, and it currently only does
code generation in parallel.

MIRAI does not attempt to do any analysis in parallel and this does hurt when it analyzes large and complicated crates
like MIRAI itself. Making things thread safe will be a challenge because of caching, sharing of sub-expressions and the
need to query the rust compiler for type information. The top-down nature of the analysis also limits how much can
be done in parallel, since the top level functions tend to overlap significantly in the functions that they call.
Even if they different threads can share a summary cache, the synchronization overhead will be significant and the 
analysis of pathological functions that are widely used will quickly cause other threads to block or (worse) to
duplicate work.

Pursuing this at the moment does not seem to be the best use of resources. Future work should probably concentrate on 
[incremental analysis](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/IncrementalAnalysis.md).

