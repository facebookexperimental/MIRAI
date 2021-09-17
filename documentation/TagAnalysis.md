# Tag Analysis

## Overview

Tag analysis is a compile-time static analysis that keeps track of information flows in programs. Information flows
from variable X to variable Y, whenever information stored in X is transferred to Y. Tag analysis attaches different
kinds of tags to values in a program to keep track of data flows for these tags. For example, taint analysis is a
special form of tag analysis that reasons about sensitive information, such as private user data in social network
service, or private keys in crypto code. Using tag analysis, a static analyzer can verify that tainted values (i.e.,
values attached with special taint tags) will never flow to specific program locations that may leak the information,
e.g., a method writing the tainted values to a public channel. Because the analysis is carried out at compile time,
the analyzer can verify non-trivial information-flow properties without any runtime overheads.

MIRAI supports a context-, field-, flow-, and path-sensitive tag analysis. Context-sensitivity and field-sensitivity
come from MIRAI's summary-based inter-procedural analysis and precise abstract heap model, respectively.
We implement the tag analysis as a data-flow analysis with a tag domain that over-approximates present and absent tags
on values simultaneously. When the data-flow analysis is not precise enough to answer queries, MIRAI generates a
propositional formula that encodes both the query and the path condition that guards the query, and uses an
off-the-shelf constraint solver such as [Z3](https://github.com/Z3Prover/z3) to answer the query.

Tag analysis is in general an undecidable problem, so MIRAI might not get sufficiently precise information to verify
information-flow properties. MIRAI's tag analysis is developed to be consistent with MIRAI's design, which avoids false
negatives (not flagging real errors), and reduces the number of false positives (flagging false errors). When the
analysis result is not precise enough, or MIRAI timeouts because the analyzed program has very complex control or data
flow, MIRAI will produce a conservative approximation of the program states and report possible errors, some of which
may be false positives. As in other static analysis, developer-provided annotations, such as loop invariants, or
simplification of the control flow in the analyzed program, could help MIRAI improve analysis precision.

## Declaring tags

MIRAI supports developer-defined tags and customizable tag propagation behavior. Tag-related types and macros are
provided by the [MIRAI Annotations](https://crates.io/crates/mirai-annotations) crate.

In MIRAI, tags are just Rust types, except that they are assumed to have at least one generic argument, the first of
which should be a const parameter of type `TagPropagationSet`. Currently, Rust's support for const generics is
incomplete. To enable such an incomplete and unstable feature only in MIRAI builds, one can use Rust's mechanism for
conditional compilation:

``` rust
#![cfg_attr(mirai, allow(incomplete_features), feature(generic_const_exprs))]
```

The code below declares a tag kind named
`SecretTaintKind`.

``` rust
#[macro_use]
extern crate mirai_annotations;

#[cfg(mirai)]
use mirai_annotations::{TagPropagation, TagPropagationSet};

#[cfg(mirai)]
struct SecretTaintKind<const MASK: TagPropagationSet> {}
```

`MASK` is used to specify propagation behavior of different program operations for the tag. For example, if bitwise-xor
can be used to “sanitize” tainted data, it will then block the taint tag. MIRAI provides a macro `tag_propagation_set!`
to create a tag-propagation set by specifying all the operations that can propagate the tag. The code below defines a
tag named `SecretTaint` that can only be propagated by equality checks.

``` rust
#[cfg(mirai)]
const SECRET_TAINT_MASK = tag_propagation_set!(TagPropagation::Equals, TagPropagation::Ne);

#[cfg(mirai)]
type SecretTaint = SecretTaintKind<SECRET_TAINT_MASK>;
#[cfg(not(mirai))]
type SecretTaint = (); // Ensures code compiles in non-MIRAI builds
```

## Attaching and checking tags on values

In MIRAI, tags are attached to values via the `add_tag!` macro, whose first parameter is a reference to the value
that is being tagged, and second parameter is a well-defined tag type. The code below attaches the `SecretTaint` tag we
just defined to a value.

``` rust
add_tag!(&value_to_be_tagged, SecretTaint);
```

To check if a value has (respectively, does not have) a tag attached to it, we can use the `has_tag!` macro
(respectively, the `does_not_have_tag!` macro). Both macros take a reference to the checked value and a tag type as
arguments, and return a Boolean value indicating the check result. A common usage is to combine them with MIRAI's
specification mechanisms such as verification conditions, pre-conditions, and post-conditions. The code below
illustrates the three mechanisms.

``` rust
// as a verification condition
verify!(does_not_have_tag!(&value_without_tag, SecretTaint));

// as a pre-condition
fn argument_must_be_tainted(msg: Message) {
    precondition!(has_tag!(&msg, SecretTaint));
    ...
}

// as a post-condition
fn result_must_be_tainted() -> Message {
    ...
    postcondition!(has_tag!(&result, SecretTaint));
    result
}
```

These annotations are equivalent to no-ops when the code is compiled by an unmodified Rust compiler. When compiled with
MIRAI, these annotations cause MIRAI to check the conditions and emit diagnostic messages if MIRAI cannot prove the
conditions to be true.

## Annotating trait methods

Traits provide powerful abstraction mechanisms in Rust, and it is natural to think about adding pre-/post-conditions to
trait methods, in a way that all the implementors satisfy the contract. For example, we can define a `TaintRemovable`
trait as follows, where `remove_taint` is the interface, but every implementor should instead implement the
`_impl_remove_taint` method.

``` rust
trait TaintRemovable {
    fn remove_taint(&mut self) {
        self._impl_remove_taint();
        postcondition!(does_not_have_tag(self, SecretTaint));
    }

    fn _impl_remove_taint(&mut self);
}
```

With the [Rust design by contracts crate](https://gitlab.com/karroffel/contracts), one can use the `contract_trait`
attribute to get rid of the boilerplate.

``` rust
use contracts::*;

#[contract_trait]
trait TaintRemovable {
    #[post(does_not_have_tag(self, SecretTaint))]
    fn remove_taint(&mut self);
}
```

See the [trait-methods crate](../examples/tag_analysis/trait_methods) for a complete example.

## Scenario I: Detect timing side-channels

Constant-time programming is a well-known discipline to protect programs---especially crypto code---against timing
attacks. A common practice is to avoid branchings to be controlled by sensitive information, because attackers could
use side-channel attacks that measure different execution times of a program to infer the sensitive information.

For example, the code below implements a compare function that is **not** constant-time, because the running time of it
depends on the length of the longest common prefix of `secret` and `public`. An attacker could construct different
values as `public` and measure the running times to infer the content of `secret`.

``` rust
// The compare function is **not** constant-time.
fn compare(secret: &[i32], public: &[i32], len: usize) -> bool {
    for i in 0..len {
        if secret[i] != public[i] {
            return false;
        }
    }
    true
}
```

The code below implements a constant-time compare function, by iterating all the integers in `secret` and `public`. The
implementation is constant-time because it avoids the early-return behavior that leaks information about `secret`.

``` rust
// The compare function is constant-time.
fn compare(secret: &[i32], public: &[i32], len: usize) -> bool {
    let mut result = true;
    for i in 0..len {
        result = result & (secret[i] == public[i]);
    }
    result
}
```

MIRAI's constant-time verification is enabled by a command-line option `--constant_time Name`, where `Name` is the tag
kind type identifying sensitive information that should not influence running time, e.g., the type `SecretTaintKind`
defined above. MIRAI reports every branch condition that has the tag used for constant-time verification. If MIRAI
timeouts or the analysis result is not precise enough, MIRAI will report all possible errors, which may contain false
positives, i.e., some branch conditions are reported to possibly have the constant-time tag, but during any real
execution of the program, these branch conditions would not have the constant-time verification tag. Providing
annotations (such as loop invariants) or simplifying the program's control flow can help MIRAI reduce the number of
false positives.

See the [timing-channels crate](../examples/tag_analysis/timing_channels) for a complete example.

## Scenario II: Track untrustworthy inputs

In public-key cryptography, the source of a public key might be untrustworthy. Also, public keys obtained from the
the outside environment might suffer from non-trivial vulnerabilities, e.g., public keys for Ed25519 might not be safe
against small subgroup attacks.

The code below illustrates a scenario, where we want to make sure that every public key used in the system is either a
key that we already know is valid, or a user-input key that goes through the `try_from` method, which checks for key
validity. We can verify this property using tag analysis: when a public key is used, we check if it does not have a
`Tainted` tag, or it has a special `Sanitized` tag that can only be attached to values via `try_from`. In practice, the
`Sanitized` type can usually be defined as a private type in the module containing `try_from`, so that developers using
this module are not able to attach the `Sanitized` tag to values, except by calling the `try_from` method.

``` rust
// A public key that we already know is valid.
// This key is defined in a way that it does not have the Tainted tag.
const A_VALID_PUBLIC_KEY: PublicKey = ...;

// Deserialize a public key without any validity checks.
fn from_bytes_unchecked(bytes: &[u8]) -> PublicKey {
    let public_key = ...;
    add_tag!(&public_key, Tainted);
    public_key
}

// Deserialize a public key. This method checks for key validity.
fn try_from(bytes: &[u8]) -> Result<PublicKey> {
    let public_key = from_bytes_unchecked(bytes);

    // Perform validity checks. Return Err if the key is invalid.
    ...

    add_tag!(&public_key, Sanitized);
    Ok(public_key)
}

// Check that `sig` is valid for `message` using `public_key`.
fn verify_msg(sig: &Signature, message: &Message, public_key: &PublicKey) -> Result<()> {
    precondition!(does_not_have_tag!(public_key, Tainted) || has_tag!(public_key, Sanitized));
    ...
}
```

MIRAI reports every verification condition that is provably false. If MIRAI
timeouts or the analysis result is not precise enough, MIRAI will report all possible errors, which may contain false
positives, i.e., some verification conditions are reported to be possibly false, but during any real execution of the
program, these verification conditions would be actually true. Providing annotations (such as loop invariants) or
simplifying the program's control flow can help MIRAI reduce the number of false positives.

See the [untrustworthy-inputs crate](../examples/tag_analysis/untrustworthy_inputs) for a complete example.

## Scenario III: Record verification status

In a blockchain codebase, there are many verification routines that check the validity of different values, including
blocks, messages, keys, etc. As pointed out by this [issue](https://github.com/libra/libra/issues/1602), it would add
clarity to record verification status in the values.

There are two common ways to record such information. One is to introduce a new type, e.g., a verified `VoteMsg` will
be typed `VerifiedVoteMsg`. The benefit is that the types would not introduce runtime overheads, but one downside is
that developers would need to refactor a large part of the code. The other is to add a Boolean field to data structures
to record the verification status, and check these fields at runtime. This approach is more flexible than static
methods, but one downside it that it introduces runtime overheads.

Using MIRAI's tag analysis, we have a third way that does not have runtime overheads, or rely on Rust's type system, in
a way that the verification recording is orthogonal to the existing code. MIRAI is is more expressive than the type
system, though it may still emit false positives in the diagnostics. We can implement this mechanism as illustrated
below: after a value has gone through a verification routine, we attach a `Verified` tag to it. For other code, where a
verified value is required, we add a condition to enforce that the value has been attached with the `Verified` tag.

``` rust
// Make sure a VoteMsg makes sense.
fn verify(msg: &VoteMsg, validator: &ValidatorVerifier) -> Result<()> {
    ...
    add_tag!(msg, Verified);
    Ok(())
}

// Send the vote to the chosen recipients.
fn send_vote(msg: &VoteMsg, recipients: Vec<Author>) {
    precondition!(has_tag!(msg, Verified));
    ...
}
```

MIRAI reports every verification condition that is provably false. If MIRAI
timeouts or the analysis result is not precise enough, MIRAI will report all possible errors, which may contain false
positives. Providing annotations (such as loop invariants) or simplifying the program's control flow can help MIRAI
reduce the number of false positives.

See the [verification-status crate](../examples/tag_analysis/verification_status) for a complete example.
