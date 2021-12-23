# Introduction

## Why MIRAI?

The origin of the MIRAI project was a comparative analysis of programming languages done to decide on which programming
language to use for implementing [Diem](https://github.com/diem/diem). A decision was made to use Rust, but the analysis
concluded that support for static analysis tools for Rust was one of the few areas where Rust did not compare well with
its competitors. The MIRAI project was started to help rectify this.

There are other efforts to create static analysis tools for Rust, with [Clippy](https://github.com/rust-lang/rust-clippy) 
being perhaps the most impactful right now. Together with the Rust type system and the excellent design of the rust
standard library and the general adoption of a functional programming style by the Rust community, it is actually quite
likely already that Rust programs will have far fewer problems than similar programs written in other languages.

Nevertheless, it is still possible to write Rust programs that terminate abruptly and disgracefully. A tool such as MIRAI
goes beyond linters, patterns and practices; moving ever closer towards verifying that code cannot terminate abruptly.

MIRAI does this by doing a reachability analysis: Given an entry point, it will analyze all possible code paths that start
from that entry point and determine if any of them can reach a program point where an abrupt runtime termination will
happen. Ideally, if MIRAI does not report the existence of such a path, it means that a mathematical proof can be
constructed to the effect that no such path exists.

In practice, it is not possible to always construct such a proof automatically, which can lead to both false positives
and false negatives, depending on circumstances and options. Nevertheless, it should be possible often enough for a tool
like MIRAI to be useful for most Rust programmers.

## Why not that other project X?

There are now quite a few other projects that are building proof constructing static analyzers for Rust that are similar
to MIRAI. For example: [Creusot](https://github.com/xldenis/creusot), 
[Crux-mir](https://github.com/GaloisInc/crucible/tree/master/crux-mir),
[Prusti](https://github.com/viperproject/prusti-dev), [RustHorn](https://github.com/hopv/rust-horn),
[Sabi](https://github.com/pandaman64/sabi) and [Smack](https://github.com/smackers/smack)

These are great projects, but they are also research efforts and consequently have to prioritize novelty.

By contrast, the goal of MIRAI is to produce a Rust compiler plug-in that fits smoothly into cargo, can ingest
arbitrary, unannotated rust code, produce actionable diagnostics with a low false positive rate, and do this so quickly
and efficiently that it can be part of every Rust developer's normal work flow, as well as part of a continuous
integration work flow. If this can be done without having to come up with novel solutions to difficult problems,
so much the better.

This [paper](https://alastairreid.github.io/papers/hatra2020.pdf) is an excellent exposition of the ambition that the 
MIRAI project is inspired by and the problem space that it finds itself in.

## Current status of MIRAI

MIRAI v1.1.* is a stable release and is expected to work in most cases. Any issues reported on Github will be
investigated and fixed as appropriate. There are currently no plans for a v2.

## How to use MIRAI

You'll need to build and install MIRAI as described [here](https://github.com/facebookexperimental/MIRAI#using-mirai).
That done, just run `cargo mirai` in the root directory of your project.

When run this way, MIRAI, will statically analyze all the code reachable from entry
points in your project. If any of these code paths can lead to an abrupt termination, you'll see Rustc-like diagnostics.

## Entry points

An entry point is a function that can be called externally, for example the main function of binary crate, a public
function of a library crate, or a unit test function in either.

Since it is necessary for MIRAI to resolve and analyze all functions that can be reached from an entry point, it
is not possible for a generic or higher order function to serve as an entry point. When you analyze a library crate,
this might mean that only unit tests will be analyzed, so there is one more reason to write unit tests.

## Reducing false positives

False positives are diagnostics that point out execution paths that terminate abruptly, which seems like bugs but are
not, because the execution paths that will never actually be executed. This does not mean that MIRAI is unable to detect
dead code branches, but rather that an abruptly terminating code path might be alive only if the function is called
with particular values for its parameters. For example, with None, rather than Some(x).

If it is the intention of the author of a function with such a path that the callers of the function should never
pass in such values, then the function may still be regarded as correct and the author will not thank the tool for
pointing out that such values will crash the function. In other words, even true positives can be false positives
in the eyes of developers.

While it is good practice to document functions in such a way that callers can easily discover which values will lead
to abrupt terminations, this is not as common as it should be. And, of course, natural language comments are not going
to help the analyzer to distinguish between intentional and unintentional crashes. Sometimes, public functions will
explicitly check that their parameters are valid and one can regard such checks as explicit documentation that is
understood by the analyzer. Unfortunately this is not common, so an analyzer cannot rely on this.

Consequently, when MIRAI analyzes a function, it regards _all_ abrupt code paths that are conditional
on the value of a parameter, as intentional parameter validity checks (known as **preconditions** in the verification 
community). These checks are added to a summary of what the analyzed function expects and does and call sites are
checked to ensure that the preconditions are not violated. Potential failures to uphold preconditions can likewise
become preconditions of the calling function.

The effect of all this is that most functions generate no diagnostics and those that do, typically have diagnostics
pointing to call sites where unknown (at compile time) non parameter values (such as input values) are passed to
functions that do explicit or implicit validity checks on their parameters.

Another way false positives are reduced is by suppressing any diagnostics that arise within the standard library or
third party code. In other words, only diagnostics that are tied to source locations within the crate being built
by a call to the MIRAI wrapper for rustc, will be surfaced.

## Incomplete analysis

When a function call cannot be resolved, or when it resolves to an implementation for which there is no MIR body (because
it is part of the standard library, or because it is a foreign/intrinsic function), the analysis of the calling function
might be incomplete, and thus imprecise (due to not applying the side-effects, not knowing the post-conditions, and not 
verifying the pre-conditions), which can generate false positives as well as false negatives. Any callers of an
incomplete function are themselves incomplete and so on until the entry point.

Another source of incompleteness are timeouts in the abstract interpreter. More about that later.

Since we want to minimize false positives, MIRAI does not issue a diagnostic for a call to a missing or incomplete
function. Instead, such calls are treated as if they are abrupt terminations. Consequently, if a precondition can be
inferred, it becomes the caller's caller's problem.

Since most code is already well tested and mostly correct, the flood of false positives
that result from incomplete analysis is quite off putting and reflects badly on the analyzer. To mitigate this,
call sites to incomplete or missing functions are always treated as unreachable, even if a precondition cannot be
inferred to guarantee this.

This is obviously not a sound thing to do, so when verification is the objective the analyzer can be invoked with 
the option `--diag=verify`. This will generate a diagnostic for every reachable source of incompleteness (i.e. the
cases where preconditions cannot be inferred), while still analyzing the function under the assumption that the call
site is unreachable.

## Library code

When library functions expect that callers will not call them with problematic values, there should be checks that the
callers respect this. And since the callers are not necessarily known, and may not yet have been written, one cannot
rely on checking the calling code to make sure they respect the restrictions.

Authors of library functions are often content as long as their code panics in such situations. The problem with this
approach is that an analyzer cannot infer intent and thus cannot distinguish between panics that happen because
argument values are wrong, or panics that happen because the library function has been coded incorrectly.

It is therefore best practice to analyze libraries with `--diag=library`. With this option, any path that panics will
generate a diagnostic, unless that path is precluded by an explicit precondition. This requires annotation of the
library source code. There are two supported ways for annotating code. The first is to use the 
[design by contracts](https://crates.io/crates/contracts) crate. The second is to use the 
[mirai annotations crate](https://crates.io/crates/mirai-annotations).

The design by contracts crate is more light weight to use and can be more approachable, particularly when teaching
verification techniques to students. The mirai annotations crate is more full featured and is also the only way
access more advanced annotations, such as tagging for taint analysis.

## Invariants

The design by contracts crate provides a way to declare invariant properties for struct fields, that need to be established
by constructors, must be maintained by mutators and can be assumed by readers. The syntax is a bit clunky because of
the particulars of Rust syntax and the constraints imposed by procedural macros.

Using the MIRAI annotations crate, there is no explicit support for invariants. The expectation is that they will
be assumed via explicit preconditions and established via explicit post conditions.

Future work may well try to make things nicer by allowing invariants to be encoded by implementing a special Invariant
trait defined in the MIRAI annotations crate.

## Quantifiers

There is currently no support for using quantifiers (for all and there exists) in annotations. This a non trivial work
item that keeps getting put off until later. Interestingly, the lack of support for quantifiers have not yet become
an actual problem because there have always been acceptable ways to work around the need for quantifiers
(usually just adding an assumption or two).

## Taint analysis

Most of the discussion above is about execution paths that might reach program points where execution terminates abruptly.
An equally important question is whether data may flow from untrusted sources to trusting sinks. Since MIRAI already keeps
track how values flow from one memory location to another, in order to reason about conditions (and thus about whether a
conditional path is feasible or not), it is well within scope to also analyze data flows.

To enable taint flow analysis, annotations are needed and the macros for these can be found in the
[mirai annotations crate](https://crates.io/crates/mirai-annotations). The basic idea is that every source of untrusted
data should be annotated to add a special tag to the data. Sinks that need to trust their data also need annotations,
typically just preconditions that check for the absence of the untrusted tags.

An interesting design point about MIRAI taint analysis is that tags can be added but not removed. This prevents accidental
removal of tags by intermediate (and possibly untrusted code). Furthermore, tag values are parameterized with a list
of operations that propagate the tags. For example, if value x has a tag that propagates via addition operations, then
value x + 1 will also have that tag.

This raises the question of how untrusted data that has been checked and found to be safe, can ever flow into a trusting
sink. The solution is to invent yet another, "good" tag and to let the trusting sinks require that either the bad tag
is missing or the good tag is present.

To prevent intermediate code from accidentally adding "good" tags, this can be made a privileged operation by making
the tag constructor private.

More details and examples can be found [here](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/TagAnalysis.md).

## Constant time analysis

Constant time analysis is a specialized form of taint analysis. It determines whether a sensitive bit of data, such as
a password or private encryption key, can influence the running time of the program (and thus leak the sensitive data
via a side-channel). This analysis is disabled by default and can be turned on with `--constant_time Name`, where `Name` 
is the tag kind type identifying sensitive information that should not influence running time,

# Abstract interpretation

## Interpreter

MIRAI is built as an interpreter that can deal with both concrete and abstract values and it is not unreasonable to
think of it as an abstract interpreter, although it departs from the usual practice in Abstract Interpretation in
meaningful ways.

The code that MIRAI interprets is the Mid-level Intermediate Representation (MIR) of the Rust compiler. This is a better
starting point than the typed abstract syntax trees that procedural macros and Clippy use because of there is a lot
less complexity in the structure of MIR and a reachability analysis does not need to look for problematic syntactic
patterns, not least because Clippy already does a good job of this.

An alternative to MIR would be use the LLVM bit-code that the rust compiler produces from MIR. Doing so, however, makes
it harder to accurately relate diagnostics to source locations. Bit-code also loses some of the typing information that
is available in MIR and this presumably makes it harder for a bit-code based analyzer to resolve trait calls that the 
rust compiler leaves unresolved until runtime.

A big downside of using MIR is that it is under specified and the design has been in flux. There are also many gotcha's
and strange conventions. It is quite striking to compare the wild world of MIR to the regular and well documented design 
of the CIL of Microsoft .NET.

## Abstract Values

The values that MIRAI operates on can be thought of as symbolic expressions from which classical abstract domain values
are computed on demand, so it is also fair to think of MIRAI as a symbolic execution engine.

It is actually somewhat rare for classical abstract domains values to be computed at all. Mostly, values stay symbolic
and the usual question to ask an abstract value is simply: are you always true or always false? If need be, this question
is answered by translating the abstract value's expression to a predicate for an SMT solver such as Z3. Most often,
the question is answered without resorting to the solver because expressions are algebraically simplified as they
are constructed. During simplification, other questions may be asked and this might involved classical abstract domains.

Algebraic simplifications are a significant source of complexity for MIRAI, but simplification is the key strategy
for warding off exponential increases in expression size (along with widening). The simplifications are heuristic in
nature and are mostly shallow and bottom up (and thus quite efficient).

There are still numerous instances of expressions increasing exponentially in size, which lead to time-outs and
imprecision. But the vast majority of expressions are well behaved and simplify nicely. The remainder are considered
bugs to be fixed one way or another.

Concrete (compile time constant) values are just a kind of expression and constant folding is part of simplification.
For the sake of modularity, most of this logic is collected into the definition of an "abstract" domain for constant
values (i.e. something with transfer functions, TOP, BOTTOM, join, widen, etc.).

Currently, there are only two other abstract domains: an interval domain and a tag domain. These are computed on demand
when a question is being asked that they might efficiently answer. Once computed, the domain values are cached.

When an abstract value becomes widened because of a loop, or because of expression size overflow, the abstract domains
are pre-emptively computed and incorporated into the resulting value. The range constraints provided by the interval
domain are added to the SMT solver's environment before evaluating a predicate.

## Environment

The interpreter uses a map from **paths** to **values** as its model of the current state of memory. The map is a
functional data structure, so it is cheap to make a copy of it. This matters when doing fixed point computations and joins.

Paths and values are intertwined: a path can contain a value and a value can contain a path. The difference is simply
that a path always represents a way to get to a memory location whereas a value can be anything. In the compiler and
programming language world a path is often referred to as a "left hand value". The MIR concept of a Place is mostly the 
same as a MIRAI path and a MIR Operand is mostly the same as a MIRAI value.

An important point about environments is that they never contain structured values. That is, if path p is the memory
location of a structure with fields a and b, then the environment will have separate entries (p.a, v1) and (p.b, v2), 
rather than a single entry (p, {a: v1, b: v2}). This helps to keep environments small and to make joins efficient, 
which really matters for performance.

A key problem with paths is that they can be abstract. For example, path a[i] where a is an array and i is an abstract
index value, represents more than one memory location at compile time. This set of locations can intersect the
set of locations of another, distinct path. For example the locations sets of a[i] and a[0] overlap at compile time
if it is not known at compile time that i is never 0.

Because of such aliasing, updating the environment with a value for a path is not simple. The MIRAI code for doing such
updates is very complex and yet not complete. In practice, however, most paths are concrete and current mechanisms for
dealing with aliasing works quite well.

## Summaries

Analyzing a called function at every call site, using the environment of the call site, enables the most accurate
analysis, but can lead to exponential complexity, redundant work done during fixed point computations, as well as
difficulties with analyzing recursive functions.

The analyzer therefore analyzes functions without knowledge of the call site specific argument values, and then caches
a summary of the analysis. The summaries are computed on demand, but once cached, a call site only has to specialize
the abstract summary with respect to the local environment. This cuts down on exponential costs because any fixed
point computations done during the analysis a called function does not need to get repeated at the call site.

A summary is a list of preconditions that need to be true at the call site in order to the summarized function to not
panic, an abstract return value, a list of side-effects, and a post-condition.

## Call resolution

Indirect calls via function pointers and traits present a challenge since they cannot be resolved without taking call
site information into account. The summary cache is therefore keyed not just with the function definition id,
but also with some call site information.

The easiest problem to deal with is when a trait call has a receiver argument that is typed with a generic type that is
required to implement a trait. As long as the call site can specialize the receiver argument type with a non generic
type, the rust compiler can be queried for the actual method that implements the trait method for this type of
receiver. The book keeping required is non trivial and the result of getting it wrong is quite painful (the rust
compiler will terminate abruptly), but there is no particular challenge here.

Of course, doing this kind of specialization means that a generic function must be re-analyzed for every different
specialization and the summary caching scheme must allow for this.

When a (higher order) function has a parameter that is a function pointer (or closure) and it calls this parameter, 
the only way to resolve this call is to know the concrete function that is used at the call site of the higher order
function. This can be handled much the same way as generic parameters: some tricky book keeping and making the
summary caching scheme deal with function parameters as well as generic parameters.

There is a problem with this, however. Function pointers and closures don't have to be argument values, but can be
embedded inside structured argument values. As long as the paths to such callables are concrete, this can be dealt with
via additional book keeping. But once function pointers are obtained from iterators over arbitrary sized collections,
things get too complicated for MIRAI in its current state and call resolution fails. 

And that is by no means the only problem. If the analysis root has a parameter that is, or contains a callable, resolution
is impossible. Likewise for an analysis root that is generic. Another difficulty arises when the callable is inside an
Option<T> where T is not known. This is obviously a problem when T is a trait with a method being called. Moreover, just
giving up on analyzing the function is not an option either because the call site might actually always pass in None, and
thus never trigger the path with the unresolvable call.

The approached used to deal with to these hard problems is to infer preconditions that preclude the unresolvable calls
from being reached, as already discussed 
[above](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/Overview.md#incomplete-analysis).

## Foreign functions

A foreign function is any function for which there is no MIR code available during analysis. These can be "intrinsic"
functions that represent extended processor instructions like SSE instructions, or system calls, calls to functions
written in languages other than Rust, or just calls to Rust standard library functions that have not been marked with the
`#[inline]` attribute.

These functions need to have some kind of "model" that can be summarized and used in the analysis when calls to them
are encountered. Models for many of the standard library foreign functions are included with the MIRAI sources and
can be found [here](https://github.com/facebookexperimental/MIRAI/blob/main/standard_contracts/src/foreign_contracts.rs).

Most of these are uninteresting because they have no preconditions and their results are inputs to the program and must
thus be treated as fully unknown by the analysis. Others are just trivial re-implementations of the library functions.

Foreign functions that occur inside third party code, or even the code being analyzed, need to be summarized by adding
a module named `foreign_contracts` to the code under analysis and providing a suitable definition there.

todo: provide a link to a detailed discussion of naming conventions.

## Path conditions

In order to determine whether an instruction causing an abrupt termination is in fact reachable from an analysis root,
MIRAI needs to track a condition that needs to be true in order to execution to reach the abrupt termination.

In the absences of loops, this is relatively straight forward: every basic block, other than block 0, is reachable only
if another block explicitly branches to it. So, starting with a path condition of true for block 0, every other block
gets a path condition that is the disjunction of the conditions that govern the explicit branches to the block. Such
conditions are the conjunction of the path condition of each predecessor block with the condition (if any) that is
part of the branch instruction.

If the path condition of a block that terminates abruptly turns out to be false, the termination can be ruled out as
a possibility and the proof of the negation of the condition can be considered to be a proof of correctness for the
claim that the analyzed code will not terminate abruptly at this point.

## Loops and recursion

todo

## k-limits

The symbolic expressions of abstract values can become very large, particularly when there is looping or recursive code
or very deep call chains. Traversing large expressions obtained from function summaries in order to specialize them
to call sites can easily become exponential in time complexity, leading to effective non termination of the analysis.

Another source of traversal complexity is intra procedural value specialization, which is done because values that
result from joins can often be simplified back to constants when used in block with a path condition that implies
the value of the join condition.

Most of the time expression simplification keeps expression sizes in check and the extra precision that results from
these traversals is essential to keep false positives at bay.

When this fails, however, the analysis must be prevented from attempting exponential traversals. This is done by imposing
a number of arbitrary limits on how large an expression can be, how deep a traversal may go, how many preconditions
a summary can have, how many times a fixed point loop may iterate and how large an environment may become.

There is also periodic checks of a timer and each Z3 solver query is subject to a 100 milli seconds time-out.

# Future work

Better support for parameterized unit tests.
Providing a counter example when failing to prove that a panic is not reachable.
Github actions to make it dead simple to run MIRAI over your Pull Requests.
Human readable function summaries.
IDE integration for better code navigation and debugging support (i.e. how did control get here?)






