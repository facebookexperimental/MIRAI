# Incremental Analysis

Ideally, Mirai should just become a regular part of the Rust Language Service (RLS) and provide diagnostics while programs
are being edited.

If this is to happen, Mirai should be fast, which is not something one typically associates with program verification
tools. Furthermore, as discussed [here]((https://github.com/facebookexperimental/MIRAI/blob/main/documentation/Parallelism.md)),
parallelism is not going to help.

As discussed [here](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/Caching.md), caching
function summaries helps to avoid some exponential behavior during analysis. Caching also helps make the analysis
incremental, which is going to be the key to integrating MIRAI into the RLS.

Even so, the analysis of even a single function body can become exponential when it contains many loops and/or makes
many calls to functions that have large summaries. Imposing
[k-limits](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/K-limits.md) helps to keep things
responsive, but at the cost of increasing the number of false negatives.

It seems interesting to pursue more incrementalism in this case, possibly by retaining the environments computed for
basic blocks, using a hash of the incoming environment of a basic block as the key.
