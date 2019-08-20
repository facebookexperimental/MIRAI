# MIRAI  [![Build Status](https://travis-ci.com/facebookexperimental/MIRAI.svg?token=uaX9rExVwSVz5FfMFphz&branch=master)](https://travis-ci.com/facebookexperimental/MIRAI) [![codecov](https://codecov.io/gh/facebookexperimental/MIRAI/branch/master/graph/badge.svg?token=q4jzL09Ahl)](https://codecov.io/gh/facebookexperimental/MIRAI)
MIRAI is an abstract interpreter for the [Rust](https://www.rust-lang.org/) compiler's [mid-level intermediate
representation](https://github.com/rust-lang/rfcs/blob/master/text/1211-mir.md) (MIR).
It is intended to become a widely used static analysis tool for Rust.

## Using MIRAI

You'll need to install MIRAI as described [here](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/InstallationGuide.md).

To run mirai, use cargo with `RUSTC_WRAPPER` set to `mirai`.
Use `rustup override set nightly-2019-MM-DD` to make Cargo use the same version of Rust as MIRAI. If you forget to do
that you'll see an error message complaining about a dynamic load library not being found.

The easiest way to get started is to first build your project in the normal way.
Refer [this link](https://doc.rust-lang.org/1.30.0/book/first-edition/getting-started.html) for details
on compiling a cargo project.
When there are no compile errors,
no lint errors and no test failures, you can proceed to the next step and run MIRAI. For example:
```
touch src/lib.rs
RUSTC_WRAPPER=mirai cargo check
```

The touch command (which needs to reference a real file in your project) forces Cargo to re-run rustc and to not assume
that it's cached error messages are still correct.

This will likely produce a lot of warnings, which you can then fix by adding annotations using this
 [crate](https://crates.io/crates/mirai-annotations). Keep running cargo check as above until there are no more warnings.

At this stage your code will be better documented and more readable. Perhaps you'll also have found and fixed a few bugs.

Set the verbosity level of output from MIRAI by setting the environment variable `MIRAI_LOG` to one of
`info`, `warn`, `debug`, or `trace`.

To go beyond this, super lint + better documentation phase, you'll need to be aware of a lot more things.

## Developing MIRAI
See the [developer guide](https://github.com/facebookexperimental/MIRAI/blob/master/documentation//DeveloperGuide.md)
for instructions on how to build, run and debug MIRAI.

## Full documentation
* [Overview of project](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/Overview.md).
* [Architecture](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/Architecture.md).
* [Design discussions](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/DesignDiscussions.md).
* [Further reading](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/FurtherReading.md).

## Road map
* Stabilize MIRAI and get rid of crashing bugs and OOMs
* Model (ghost) variables
* Quantifiers
* Explicit loop invariants
* Structure invariants
* More standard library contracts
* Upgrade log message that affect soundness into compiler warnings 
* Publish MIRAI to crates.io
* Support linting interfaces
* Tutorials and worked examples
* Loop discovery
* Loop invariant inference
* Make MIRAI work on Linux

## Join the MIRAI community
<!-- * Website:
* Facebook page:
* Mailing list
* irc:  -->
See the [CONTRIBUTING](https://github.com/facebookexperimental/MIRAI/blob/master/CONTRIBUTING.md) file for how to help out.

## License
MIRAI is MIT licensed, as found in the [LICENSE](https://github.com/facebookexperimental/MIRAI/blob/master/LICENSE) file.
