# Overview

## Taint analysis

In brief, the basic idea of taint analysis is that certain functions are annotated as sources of taint, which typically
means that their return results are treated as tainted by the static analyzer.

Other functions are annotated as unsafe sinks of taint, which typically means that it is a programming error if a value
produced by a source of taint can reach a parameter of an unsafe sink.
For example, if a user controlled input can reach a call to a shell exec function, then an attacker can potentially use 
a malformed input to take over or damage a server that contains this kind of flow.

Typically, code guards against this by parsing and transforming all external inputs into something that cannot cause
harm. For example strings that can become part of SQL queries or HTML requests are usually “sanitized” to avoid these
kinds of “injection” attacks. A taint analyzer will thus also have to have a way of annotating functions as sanitizers
and will allow a flow from a sink to source to happen as long as it is sanitized along the way.

Of course, things are more complicated in practice since there can be multiple kinds of taint and sinks may be unsafe
only for some kinds of taint and not others, while sanitizers may remove only some kinds of taint and not others. 
There are also many ways for taint to flow, for example a tainted value may become part of an aggregated value, which 
should then be treated as tainted as well. There are also flows via side channels, such as when a tainted value is used 
in a condition that allows untainted (private) data to flow to an unsafe sink for that kind of data.

## Protocols

Deciding whether or not a taint flow is safe is clearly an example of a simple protocol that can be modeled by a state 
engine (which can be encoded as part of a protocol specification). The static analyzer uses annotations to identify 
state transitions and effectively verifies that the code under analysis faithfully implements the protocol.

One can well imagine that there will be other protocols for which we'd like to verify that our implementation code 
adheres to. Typically, there can also be specialized analyzers that read protocol specifications and verify that they 
enforce various desirable properties if faithfully implemented. Such analyzers are out of scope for this project.

The main point for this project is that it should be general enough to verify the faithful implementation of 
protocols other than just taint analysis.

## Verification is not on the table

General verification aims to verify that an implementation faithfully implements a “complete” specification. A program 
that has been verified in such a way is provably correct in every sense of the word. Creating such a verifier is a 
[“grand challenge”](https://www.theregister.co.uk/2004/06/14/grand_challenge_compsci/) and we'll leave that for 
others to figure out.

## Error checking

A more modest goal is to find and report code sequences that violate simple implicit and explicit specifications, 
such as any expression that causes a panic or a false assertion.

A taint analyzer that is sufficiently precise for it to be used as a check-in gate will also track control flow 
precisely enough to identify many of these kinds of errors. We would gain nothing from explicitly excluding such checks 
from our analysis and should thus add them as an additional scenario.

## Minimizing false positives

False positives are the bane of any static analyzer. If code is complicated enough it invariably sets up subtle 
conditions that guarantee that certain code paths are never executed in a state where an error can occur. It is 
typically beyond an analyzer to automatically discover these conditions and their implications. An analyzer can 
then either err on the side of safety and assume that such an execution can occur (and thus flag an error that is a 
false positive), or it can use various heuristics to try and avoid flagging too many errors, leading in turn to false 
negatives (not flagging real errors).

For this project, I expect that we'll prioritize avoiding false negatives over avoiding false positives and that we'll 
require users of this tool to be prepared to add sufficient assertions to our code bases to allow the analyzer to 
discover all the conditions necessary to prove that an error state can never be reached. This will be a significant tax 
on developers, but will also encourage good coding practices and help to document the code. It is conceivable that such 
investments will pay handsome dividends in the long run.

To minimize the annotation burden that is will impose on developers, it is important to make the reasoning of the 
analyzer as powerful and precise as we can manage.

## Precision

A key feature of Rust is that it makes data immutable by default and prevents pointers to mutable data from being 
aliased. This makes it possible for an analyzer to track the contents of the heap with much greater precision than is 
the case when analyzing almost any other language in general use for systems level programming.

We should go beyond the static analysis techniques in common use and attempt to faithfully model the heap. We should 
also avoid techniques that abstract over data in a way that loses precision. For example, every abstract value in the 
analysis should always track the operator and operands from which it was constructed and the path conditions that 
applied at that time. When the abstract view (domains) of the value (such as, this is an integer value) is not 
sufficient to disprove an error condition then the expression tree should be simplified to remove any parts that come 
from infeasible paths and the resulting expression should be incorporated into a proof condition that is given to a 
general constraint solver such as [Z3](https://github.com/Z3Prover/z3).

This will have a cost but developers should be able to provide hardware resources towards it that today can go vastly 
beyond what was feasible a decade ago. As long as developers can incorporate MIRAI into their build and development 
process in way that enables rather than impedes them, we should not compromise on precision.

## Modularity

The key to good performance is to make the cost of the analysis proportional to the size of a code change rather than 
the size of the entire code base. At the very least, compiling a crate should not involve the re-analysis of other 
crates. This is not possible in general if there are cyclical dependencies between crates, which can be hard 
to avoid in realistic projects.

To deal with this, it will be necessary to track dependencies at a fine level. We should store a “summary” of every 
method/function and static variable in some kind of data base (possibly serialized into or along side crates) and we 
should use a stable naming scheme to identify and retrieve these summaries. A summary will also include references to 
other summaries and if these form a cycle all of the connected components will have to re-summarized until a fixed point 
is reached. This can cause the analysis of a single component to degenerate into an analysis of a portion of the code 
base that greatly exceeds the size of the single component.

To deal with this in an interactive setting (i.e. during code editing) it may be necessary to ignore cycles. It may 
also be necessary to ask developers to limit cycles. Where possible, however, the analysis should attempt to prune 
the dependencies of a called function/method by taking into account the arguments at the point of call.

Keeping the analysis fast and modular is likely to be one of the key challenges of this project. Initially, we'll forbid
cyclical dependencies between crates.
