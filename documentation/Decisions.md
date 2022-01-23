# Decisions

## Target the full Rust language
### Positives
Reduces obstacles to adoption.

Tool can be validated by running over large existing code base.

Provides a path to inclusion in standard suite of Rust development tools.

### Negatives
Large upfront investment, long time to market.

Rust is complicated and still rapidly evolving. There is no standard to refer to when tricky semantic questions arise.

The size and complexity of the language reflects in the analyzer and makes much more likely that the analyzer has
visible bugs and shortcomings. This makes it hard to get programmers to trust the tool as readily as they trust the
compiler and type system.

### Alternatives
#### Subset
For example: only safe code, no threads, no async, no foreign code.
#### Subset with annotations
As above, but also require programmers to explicitly annotate code with correctness assertions and invariants.
#### Full language with annotations
Require programmers to explicitly annotate code with correctness assertions and invariants.
### Compromise
MIRAI allows explicit annotations without requiring them.

## Target all Rust programmers
### Positives
Increases the value of the analyzer. Makes community adoption more likely.
### Negatives
Much higher bar for documentation and analyzer output. Much higher risk of failure.
### Alternatives
#### Target only programmers that have prior experience in verification techniques
The formal-methods community.
#### Target specialized programmer communities where correctness is super important
Such as security researchers and cryptologists.
### Compromise
MIRAI targets all programmers by default, but has options that can be used by specialists.

## Minimize false positives
### Positives
False positives are hard to explain to the general programmer community and decreases their estimation of the
value and quality of the analyzer.
### Negatives
There is a trade-off between false positives and false negatives. Minimizing the former tends to increase the latter.
Failure to catch a real bug calls into question the value of running the analyzer in the first place.
### Alternatives
#### Eliminate false negatives
This is only suitable for specialized user.
#### Increase precision
This increases complexity, risks non-termination, risks out of memory errors and makes the analyzer unattractive to
general programmers.
### Compromise
MIRAI provides options to run a sound analysis (given some assumptions). MIRAI is built to reason precisely and
uses k-limits to deal with non-termination and memory errors.

## Flow sensitive analysis
MIRAI retains full precision when joining forward conditional branches.
### Positives
The analysis is more precise and simple examples almost always work in the way non-specialist programmers expect.
### Negatives
Branch conditions often grow exponentially. Dealing with branches in the analyzer becomes quite complicated.
### Alternatives
#### Treat all join points uniformly.
#### Analyze at the AST level and provide special case handling for some constructs.
### Compromise
MIRAI's main abstract domain keeps track of symbolic expressions. The transfer functions of this domain does
algebraic simplification. Live with the complexity.

## Just find panics
By default, MIRAI does an inter-procedural reachability analysis to find code paths that might panic at runtime.
### Positives
Runtime correctness checks become implicit correctness assertions that can be checked at compile time. A wide variety
of conventions can be accommodated this way. Parameterized (fuzzy) unit tests fit nicely into this. Programmers are
more likely to write correctness assertions if they have runtime semantics and provide test coverage.
### Negatives
It is difficult to distinguish between parameter validation checks and internal consistency checks. This makes false
positives and false negatives more likely, even when the analysis is very precise.
### Alternatives
#### Explicit correctness assertions
Including invariants and quantifiers. Model fields, type state, and so on.
#### Pluggable analyses
Provide a way for specialized programmers to customize the analyzer for their use case.
### Compromise
MIRAI uses precondition inference to limit false positives due to parameter validation code and
provides an annotation library that can be used to provide explicit correctness assertions that do not promote to
preconditions.

## Don't unroll loops
Loop bodies are always analyzed via a fixed point loop, even if the number of iterations is known at compile time.
### Positives
No need to explain why some loops are more precisely analyzed than others. Analyzing loops via a fixed point is already
fiendishly complicated, so don't add more complexity.
### Negatives
Simple loops on data known at compile-time, such as found in non parameterized unit tests, cannot be precisely analyzed 
and hence assertions in the unit tests show up as "maybe false", even when the test and the code under test is clearly
correct.
### Alternatives
### Include the analyzer inside a partial evaluator that precisely executes non parameterized unit tests.
This was done for JavaScript in the [Prepack](https://prepack.io/) project.
### Compromise
MIRAI requires annotations to provide the prover with assumptions about the initial state of any iteration of a loop
body. Non parameterized unit tests need to be annotated. Some simple patterns, such as initializing all elements
of an array to a constant value, are understood and precisely modeled.

## Model the heap as a set of (path, value) pairs
Path closely resembles a Place in MIR. It is not necessarily unique because it can be a reference to another
path, an index into a collection, or even just an offset from a pointer. Whenever possible, value is a representation
of a primitive value, but it could also be a structured value that is unknown in the current environment.
### Positives
This also works for local variables and parameters. Joins are straight forward. This representation of the memory
tends to be sparse, which makes it feasible to use it in function summaries.
### Negatives
Distinct paths may be aliases of each other, which requires a lot of complexity in the form of path canonicalization and
weak updates. Paths are based on MIR places and these can denote collections/structs rather than simple values. This
means that in some cases the value of a (path, value) pair is an unknown collection or struct. This makes function 
summaries tricky since Rust level type information is required to make sense of unkown structured parameter values. 
Value transmutation (re-interpret casts) is also very tricky to deal with.
### Alternatives
It is hard to think of good alternatives. If the analysis can become imprecise, paths can be kept simple by making
their corresponding structured values fully abstract. In the case where the analyzer is embedded in a partial evaluator,
however, it seems more convenient for the evaluator to model the heap in a form that is very close to the actual
runtime structure of the heap. [Prepack](https://prepack.io/) was built in this way because it started out a concrete
evaluator (like MIRI) which was extended to also deal with abstract values.

## Precondition inference
When the entry path condition of a basic block that causes a runtime panic can be forced to be false by a choice of
one or more parameter values, the relevant parts of the condition is promoted to a precondition of the current function.
### Positives
In the code I've seen, almost every panic is part of a parameter validation check. Inferring preconditions cuts down
on false positives by making it unnecessary to add explicit precondition annotations that merely repeat the logic
of the parameter validation checks. Also, parameter validation checks can happen after local state has already been
altered and moreover, these checks can be part of the language semantics. Duplicating such logic in preconditions is 
tedious at best. At worst, it can be impossible to state such conditions as preconditions without resorting to
quantifiers. Precondition inference also largely removes the need for explicit invariant annotations. 
### Negatives
Untangling preconditions from path conditions is tricky and can result in preconditions that cannot reasonably be
satisfied by the caller (either because the callee has a real bug, or the analysis of the callee is imprecise).
### Alternatives
#### Explicit annotations
This is the most common approach and it has the advantage of making things explicit and forcing careful design early on.
#### No summaries
If called functions are always inlined (with special handling of recursion, of course), the distinction between caller
and callee disappears and preconditions are not needed. The tricky and not quite satisfactory code for untangling
preconditions from path conditions go away. On the other hand, exponential analysis time becomes much more difficult
to avoid.

## Whole program analysis
Given a target to analyze, MIRAI extracts a set of entry points and then analyzes each entry point in a top-down
fashion by de-virtualizing (resolving) all calls and effectively in-lining them (by specializing summaries).
### Positives
Without this approach it is virtually impossible to accurately analyze unannotated code. Inlining specialized summaries
of actual code is more precise and efficient than dealing with axiomatic definitions of abstract functions. It also
does not run into the problem of assuming that all third party code adhere to the axioms.
### Negatives
De-virtualization involves a lot of very tricky code, which makes the analyzer brittle and reduces trust in its
correctness. Generic code and higher order functions become hard to summarize and must be monomorphized with respect
to both generic arguments and arguments containing function values. This reduces the effectiveness of summary caching.
### Alternatives
#### Extensive annotations to deal with generic and function arguments
This is a known pain point in past projects that I'm familiar with.
#### Angelic assumptions
It is often quite reasonable to assume that code which is not part of the project being analyzed is correct and that
every called function has no preconditions and establishes no post conditions. This is a lot less reasonable when
call sites cannot be annotated with useful post conditions (because the goal is to analyze unannotated code).

## Provide cargo subcommand
cargo mirai
### Positives
Having a cargo subcommand makes it possible to compile dependencies with compiler flags that help MIRAI, while
compiling the project to analyze with mirai rather than rustc.
### Negatives
While the default case is very easy to use, setting options for MIRAI is a bit clunky. Also, this ties MIRAI to
cargo, whereas the major expected use case (running as part of a continuous integration system) might not involve
cargo at all.
### Alternatives
Use cargo as is, via the RUSTC_WRAPPER environment flag.

## Plug into Rust compiler
The main routine mirai executable is a stub that invokes the rust compiler with a call back that invokes MIRAI as
part of the rust compilation.
### Positives
MIRAI does not have to do scanning, parsing, macro expansion, type analysis and syntactic desugaring. MIRAI has
access to the compiler's symbol table and can leverage the compiler to de-virtualize functions.
### Negatives
MIRAI needs a nightly build of the compiler to plug into. The interfaces to get hold of compiler data are ill-defined
and unstable. The data structures and performance characteristics of the compiler is dominated by type checking
and code generation. The information needed from the compiler for analysis is often private or very awkward to get hold
of. Debugging a problem that arises because of a change in the compiler is painful. Installing MIRAI is
trickier because of the dependency on a nightly build of the compiler.
### Alternatives
#### Write a clean compiler specialized for static analysis
Not a good idea for such a complicated language, but this is pretty much what has been done for C++.
#### Analyze the output of the rust compiler.
For example LLVM bitcode. This is not a terrible idea, but see 
[Why plug into the Rust compiler?](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/WhyPlugIn.md).

## Use MIR
The Mid-level Intermediate Representation is the last intermediate data structure produced by the rust compiler before
it generates target code. It is effectively an abstract machine language. MIRAI is an abstract interpreter for MIR.
### Positives
A lot of complexity that is orthogonal to static analysis is removed when analyzing MIR, but little if any information
is has been lost at this point. After code generation, the data used for name resolution and type analysis is all gone,
and it is costly to recover.

Running as part of the compiler means that the analyzer can use the compiler's diagnostic reporting services. Any
performance enhancements due to incremental compilation support and parallelism in the compiler also accrue to the
analyzer (which otherwise would have to duplicate this complexity in its own code).
### Negatives
MIR is ill-defined and at a level where some instructions have very complicated semantics that depend on type
information in deep and complicated ways. MIR is also unstable and changes to MIR frequently require rewrites of
the analyzer. Moreover, the compiler's type system frequently resorts to abstraction that loses information that is
statically available. This forces the analyzer to maintain a parallel type system. Querying the compiler's type system
requires the analyzer to respect preconditions that are hard to figure out and sometimes impossible to satisfy.

MIR is also not uniformly available, whereas a lower level representation such as LLVM bitcode is available for many
more functions.
### Alternatives
#### Use LLVM bitcode
But see
[Why plug into the Rust compiler?](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/WhyPlugIn.md).
#### Lower MIR into a well-defined and stable LIR where operations are simple
For example, the Common Intermediate Language of .NET.

This might be the best option, but it has not been explored. A downside is that much of the work need to monomorphize
and devirtualize will duplicate work that the analyzer needs to do. The code to lower MIR to LIR will also be exposed
to the complexity and instability of MIR, so the overall pain the project might not be less than that of the current
approach.

## Auto summarize
MIRAI constructs summaries of monomorphic functions (concrete type arguments and known function arguments). A summary
is a list of inferred preconditions, a list of side effects to the heap and to mutable reference parameters, a result
and a post condition.
### Positives
Inferring such summaries makes it possible to analyze unannotated code. Caching the summaries helps to tame exponential
complexity. Summaries can be made quite precise by using symbolic expressions as abstract values.
### Negatives
Summaries can be quite large and specializing a summary with respect to the actual parameter values of a call site
can be very costly (the bulk of analysis time spent doing just that). Using monomorphic summaries reduces the
effectiveness of the summary cache.

Many lower level functions reachable from normal Rust code are intrinsic, foreign or do not have MIR because they are
non inlinable parts of the standard library. These functions cannot be auto summarized, so there is still a need
for explicit summaries.
### Alternatives
#### Inline function calls
This is in many ways simpler than monomorphizing and caching. But inlining loopy code can easily lead to exponential
analysis time because deeply nested fixed points are recomputed repeatedly, whereas with summaries they are computed
once and then re-used.
#### Programmer provide summaries
If the code is required to be annotated, summaries are effectively provided by the programmers.
#### Polymorhpic summaries
Use explicit axiomatization of generic parameters (i.e. trait constraints) and function parameters to derive
summaries for functions as written by the programmer. This works best when programmers are expected to explicitly
annotate code. Quantifiers quickly become essential.

## Persistent summaries
MIRAI summaries are serializable and there is a mechanism for constructing summaries from explicit annotations provided
separately from the source code being analyzed. A set of such summaries are constructed when building MIRAI and the
persisted serialization of the summaries is bundled with the mirai binary.
### Positives
There is a way to provide summaries for intrinsic, foreign and standard library functions.
### Negatives
Summaries have to be monomorphic and can't contain any rust compiler data structures. Function names must be in a form
that does not include compile dependent ordering.
### Alternatives
#### Use Rust as the persistence format
This removes constraints on what can be expressed in a summary, but bundling a rust file with the mirai binary and then
compiling it when the analysis starts is currently not possible.

If all code to be analyzed can be required to be programmer annotated, summaries expressed via Rust annotations can be
bundled with the source code and conditionally compiled when the mirai configuration flag is set. I.e. much like
the way intrinsics are handled on target platforms that do not support them.

## Abstract Interpretation
MIRAI is structured as an abstract interpreter over MIR instructions.
### Positives
The interpreter can directly use the rust compiler's data structures. The subtle semantics of MIR can be addressed
operationally rather than by translation from MIR to an intermediate verification language. Because the semantics
of MIR is encoded into the interpreter, it is likely more performant than any alternative.
### Negatives
A lot of the complexity of the abstract interpreter could be avoided by a translational approach. It is not clear
which approach is simpler overall.
### Alternatives
#### Translating MIR into intermediate verification language
For example [Boogie](https://github.com/boogie-org/boogie)
#### Symbolic execution
Much of what happens in MIRAI is actually just symbolic execution. An alternative would be to do without
abstract domains.

## Symbolic expression domain
The abstract domain used by default uses a symbolic expression as its representation. 
See [Abstract Values](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/AbstractValues.md). 
### Positives
The most precise way to specify which values an expression can result in is the expression itself.
### Negatives
Determining whether a concrete value belongs to an expression domain element is costly and sometimes undecidable.
Likewise for various other domain operations. MIRAI implements these operations by translating the operation into
an SMT solver expression and then using the solver to determine the result. This is subject to a small time-out
(100 ms) and can be non-deterministic.
### Alternatives
Abstract interpreters typically use specialized domains that are much easier to reason about.
### Compromise
MIRAI constructs an interval domain (or if appropriate, a tag domain) from the expression of an expression domain
element before it resorts to doing an SMT solver query.

## Simplify symbolic expressions
The transfer functions of the symbolic expression domain attempt to simplify the resulting expression using 
heuristically chosen algebraic simplification rules.
### Positives
These rules are unreasonably effective in practice, so many queries end up being trivially true or false. The
simplification rules also help to keep expressions small, which is a big performance win.
### Negatives
There are many rules and some of them are complicated. Great care must be taken to ensure that the rules are sound,
that they don't interfere with each other and that they don't incur costs that are related to the size of the
expression being simplified. A lot of this code duplicates what happens inside SMT solvers, which is suboptimal
because these solvers have been heavily optimized over decades and are very hard to beat.
### Alternatives
#### Always use an SMT solver to simplify expressions
A good idea in principle, but the cost of translating an expression to the input format of the solver is significant.
This also makes the analyzer more non-deterministic.

## Devirtualize
Calls to virtual functions are resolved to particular implementations by tracking the concrete types of argument values
during the analyses of the caller and then obtaining a specialized summary for the virtual function using the actual
argument types (along with actual generic arguments and the function values reachable from arguments).
### Positives
Resolving a virtual function to a particular implementation makes the analysis of the caller more precise. Furthermore,
if no annotations are available, it is quite difficult to arrive at an auto summary because the compiler's query system
does not make it easy to efficiently traverse the whole program to find every function that might implement the virtual
function.
### Negatives
Method resolution is very complex in Rust and still evolving. This means that the Rust compiler's query system must be
used to do the resolution, which makes the analyzer brittle because the compiler's query system panics if subtle and
undocumented invariants are not satisfied.
### Alternatives
#### Auto summarize virtual functions by joining the summaries of all function that implement virtual functions.
This is both imprecise and difficult to do, as noted above.
#### Require programmers to provide summaries of virtual functions
This a big burden because there are lots of virtual functions. It is also runs into the problem that it is unsound
unless every implementation of the virtual function is verified to conform to the summary.

## Use automated theorem prover (Z3)
The analyzer almost always needs to know nothing more than whether an expression is satisfiable or not, so we just
use an SMT solver (Z3) to do this.
### Positives
Answering such queries is a sweet spot for SMT solvers. Duplicating all of that logic inside the analyzer makes no 
sense.
### Negatives
The Expression types of the analyzer cannot be used by Z3 and vice versa. The consequent serialization presents a
cost in time and memory that is significant enough that the analyzer does its own simplification before involving the
SMT solver. Also, the SMT solver is heuristic and this introduces non-determinism.
### Alternatives
#### Run an abstract interpreter over the expression in question.
This is already done during expression simplification in cases where the Interval Domain might be of help. Additionally,
taint tracking is done solely using the Tag Domain (not least because Z3 has no theory that is a good match for that).

## Avoid quantifiers
The MIRAI expressions encoded as SMT (Z3) expressions contain no quantifiers.
### Positives
Without quantifiers, Z3 mostly just works as one would expect. Also, in the absence of explicit annotations, quantifiers
have to be inferred, which is a tricky business. Not implementing quantifiers for V1 of MIRAI made the project more
tractable. Perhaps surprisingly, there has been little impact on the ability of MIRAI to reason about code in the
absence of explicit annotations. My best guess about why, is that the presence of widened loop variables in the SMT
encoding effectively Skolemizes the expressions.
### Negatives
It is sometimes necessary to make assumptions inside loop bodies, not least because inferred preconditions drop
terms containing widened variables, which can result in preconditions that are too strong for callers to uphold.
### Alternatives
#### Infer quantifiers
#### Recognize Iter.all and Iter.any as quantifiers

## Data flow analysis
MIRAI provides a mechanism to use explicit annotations to tag values at their source and then to check for their
presence or absence at annotated sink points. It is also possible to designate all control flow conditions as sink
points.
### Positives
Annotations provide a highly customizable way to create tagged values and to control how tags propagate to values
computed from tagged arguments.
### Negatives
This needs annotations by specialists and it is easy to mess it up.
### Alternatives
#### Provide a way to plug in custom analyzers
#### Serialize analyzer state for downstream tools
