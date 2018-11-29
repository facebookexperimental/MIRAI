# Mirai  [![Build Status](https://travis-ci.com/facebookexperimental/MIRAI.svg?token=uaX9rExVwSVz5FfMFphz&branch=master)](https://travis-ci.com/facebookexperimental/MIRAI) [![codecov](https://codecov.io/gh/facebookexperimental/MIRAI/branch/master/graph/badge.svg?token=q4jzL09Ahl)](https://codecov.io/gh/facebookexperimental/MIRAI)
Mirai is an abstract interpreter for the [Rust](https://www.rust-lang.org/) compiler's [mid-level intermediate
representation](https://github.com/rust-lang/rfcs/blob/master/text/1211-mir.md) (MIR).
It is intended to become a widely used static analysis tool for Rust.
The initial focus will be on taint analyis.

## Building
See the [developer guide](https://github.com/facebookexperimental/MIRAI/blob/master/documentation//DeveloperGuide.md)
for instructions on how to build, run and debug MIRAI.

## Full documentation
* [Overview of project](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/Overview.md).
* [Architecture](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/Architecture.md).
* [Design discussions](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/DesignDiscussions.md).
* [Further reading](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/FurtherReading.md).

## Road map
* Set up visitor infrastructure for MIR (Early December)
* Provide a way to store and retrieve function summaries (Late December)
* State tracking and memory operations (January)
* Design Abstract Domain abstraction and implement some domains (February)
* Full scale Abstract Interpreter (March, April)
* Expression simplifier
* Hook up SMT solver
* Work on scalability
* Deploy Mirai in the build system of a large project
* More domains and refined diagnostics

## Join the Mirai community
<!-- * Website:
* Facebook page:
* Mailing list
* irc:  -->
See the [CONTRIBUTING](https://github.com/facebookexperimental/MIRAI/blob/master/CONTRIBUTING.md) file for how to help out.

## License
Mirai is MIT licensed, as found in the [LICENSE](https://github.com/facebookexperimental/MIRAI/blob/master/LICENSE) file.
