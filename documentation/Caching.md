# Caching

Initially it seemed that persistently caching summaries would enable significant savings by making it unnecessary to
reanalyze code that has not changed from one run of MIRAI to another. It turned out, however, that finding and
integrating a high performance, in-memory, persistent key value store that can be updated from multiple processes
without incurring significant synchronization overhead, is easier said than done.

Furthermore, pre-emptively producing and caching summaries for every function in every referenced crate, is 
very expensive the first time around since most of the code analyzed would not be of interest to the project actually
being analyzed. Instead, it turns out to vastly better to just analyze functions that are actually reachable
from the project being analyzed. 

Since top-down analysis also turned out to be a better way of analyzing higher order
and generic functions, MIRAI does not persist summaries in caches associated with crates.

Instead, when MIRAI runs over a package target, it does a top-down analysis and computes summaries on demand whenever
it encounters a call site where an un-summarized function is called. During summarization, the actual argument
types, generic arguments and function constant arguments of the call site are used during the analysis and hence
the resulting summary is cached with a key that incorporates these elements. 

When running as part of something like the Rust Language Service, it would make sense to keep a project cache around for
duration of the session. To enable cache invalidation when a referenced function changed its summary it will be 
necessary to store inverted call graphs along with the cache.
