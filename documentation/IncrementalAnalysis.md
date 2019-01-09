# Incremental Analysis

Ideally, Mirai should just become a regular part of the Rust compiler and even of the Rust Language Service.

If this is to happen, Mirai should be fast, which is not something one typically associates with program verification
tools. It is by no means easy, but with judicious use of concurrency and caching most hard problems can be dealt with.

The caching will be provided by a persistent key-value store that is associated with every binary and that is loaded
into memory on demand. Assume for the moment that a prior analysis has already been done and that the code is being 
recompiled after a relatively small number of changes.

If the source of a function has changed, it is to be re-analyzed. If the resulting summary is the same as the one already
in the cache, no further action is required. If not, however, every function that used the old summary must be
re-analyzed and if any of those functions now have new summaries, any of the functions that depended on them must be
re-analyzed and so on. In principle this can lead to exponential blow-up of the analysis, but assuming that head of
the programmer making the change did not blow up, it is more likely that effects of the source changes will be
much more localized.
 
It is important, however, to reason precisely and not to introduce dependencies where there are none. A typical trap
comes with indirect function calls such as Trait calls in Rust. A widely used trait can have a method that is
implemented by thousands of distinct functions. If a change to one of those functions implies that every function
that calls the trait method has to be re-analyzed, we will not only produce bad analysis results but we'll take a very
long time to do so.

Clearly, we cannot afford to record a dependency between every function calling a trait method and every function that
implements that method. We can, however, introduce an indirection by providing trait methods with their own summaries.
The callers of the trait method then only need to get re-analyzed if the trait method's summary changes. Functions that
implement trait methods will have to honor the post conditions of the trait methods and will be unable to add any
preconditions. This does have the implication that trait methods have to be annotated somehow to provide useful
summaries to their callers.

todo: write stuff about fixed points