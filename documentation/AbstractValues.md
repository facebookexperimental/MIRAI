# Abstract Values

The basic business of a static analysis tool is to reason about the behavior of a program fragment when executed in an 
abstract state that represents all the possible concrete states that apply whenever the fragment is reached. Just like a 
concrete state is made up, among other things, from concrete values, an abstract state is made up, among other things, 
from abstract values and an abstract value is basically the set of all of the corresponding concrete values that could 
be part of some valid concrete state.

Of course, no value is an island and the separate abstract values that make up an abstract state are not independent, 
but we'll mostly gloss over this by using programmer supplied assertions/invariants to constrain things sufficiently to 
allow reasoning to prove that the program fragment behaves as we expect. So, from now on we think of an abstract value 
as a set of concrete values that contains all of the concrete values that can reach the fragment, as well as some values 
that actually will never reach it. That is where false positives come from.

Another problem is that the set of concrete values corresponding to an abstract value is often infinite in size, so we 
need ways to represent infinite sets. Typically we do this with a predicate. If we allow arbitrary predicates we can 
constrain the set to be very close to the actual set, but such predicates can be hard to reason about and we run into 
undecidable questions. Consequently, we often prefer to use specialized classes of predicates about which we can reason 
deterministically in polynomial time, but which define value sets that contain more values than we want. In Abstract 
Interpretation literature the power set corresponding to a given class of predicate is called an Abstract Domain.

An abstract domain always contains a predicate that corresponds to the universal set (known as the Top element) and a 
predicate that corresponds to the empty set (known as the Bottom element). An abstract domain also provides operators 
that correspond to the operators that can be used on concrete values and these operators must maintain the property that 
the domain element that results from an operation on one or more other domain elements must include all of the values 
that may be obtained by performing the same operation on concrete values from those other domain elements. This 
guarantees that anything that can be concluded from operations on abstract domains is also true for the results of all 
possible corresponding concrete operations. Of course, one should always be careful to remember that such conclusions 
are approximate and cannot be inverted.

The class of predicates that belong to an abstract domain should form a lattice and this can be useful to find the 
parent of a given predicate, since this predicate will correspond to a larger set of concrete values and thus correspond 
to a less precise, and thus more abstract value. This is useful when an unbounded number of expression executions need 
to get summarized as a single abstract value, which usually happens in fixed point computations, which we'll not discuss 
further in this document.

## Expression Domain

The most precise way to specify which values an expression can result in is the expression itself. Let's call the 
abstract domain that is defined by such expressions the Expression Domain. The operations for this domain result in 
new expressions that just encode the operands and operators. At the very least this is useful for error messages.

The questions we may want to ask about the values of an Expression Domain element are in general undecidable, but in 
practice many questions can trivially be answered by tree pattern matching heuristics. A more heavyweight, but also more 
powerful heuristic approach is to encode the question in a form that a theorem prover like Z3 can (sometimes) answer. 
This can be done on demand and the result can be cached for use if the same question is asked again. The downside 
of this is that the behavior of the analyzer will become non-deterministic. (This does not seem to be a problem
in practice.)

Of particular interest in this domain is the common pattern of creating an expression that is the conditional join of 
two expressions, for example the value that results from the expression if c { e1 } else { e2 } where c is an unknown
value. In practice such values are often referred to in a path where c is actually known and so the abstract value can
be simplified to e1 or e2 using the Expression Domain. This use of path sensitivity is both cheap and surprisingly 
effective.

If the heuristics produce an answer, the answer will typically be precise because it is based on the actual expression, 
not an abstraction of it, so this is the answer that we'll prefer. If the heuristics fail, however, we have make do with 
an imprecise answer. To get the answer, the analyzer can ask the domain element to project itself upon an element of a 
less precise domain. (This would be done lazily and cached).

Since the answer from the less precise domain is a conservative over approximation some caution is 
needed before relying on it to issue a warning about a possible problem. In such cases, the analyzer can query a 
progression of more precise (but more expensive) domains and issue a warning only if all domains agree. This not just
be done for the faulty expression, but also for each conditional along the path that leads to the expression, so that
infeasible paths can be discovered and eliminated.
 
Even then, the analyzer can decline to issue a warning but instead annotate the current function with a precondition 
that requires callers to not supply argument values that could trigger the warning. When the code is really at fault, 
there will ultimately be a call site where the precondition is unconditionally violated and now the analyzer can 
confidently issue a warning along with a detailed explanation of how that values reaches an operation that causes a 
problem.

Propagating a precondition based on an abstract value can be a hard problem, but heuristics based on pattern matching 
of expression trees, such as found in the Expression Domain, should work well in many cases.

## Other domains

The less precise domains are well covered in the Abstract Interpretation literature and will be added to MIRAI as 
needed.

An easy domain is a Interval domain, where the predicate is of the form c1 <= v <= c2. 
This is usually good for checking index out of range errors and to check for arithmetic overflow.

Hopefully, future contributors to this project may find it interesting to add more abstract domains. As long as all 
domains expose the same set of operations and queries and perhaps some kind of cost estimate, it should be very easy to 
just plug in a new abstract domain.

Right now, MIRAI implements the Interval domain, a special domain for tracking tags, a domain for tracking compile
time constant values and a domain for tracking Boolean values.

