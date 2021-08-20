# MIRAI [![codecov](https://codecov.io/gh/facebookexperimental/MIRAI/branch/master/graph/badge.svg?token=q4jzL09Ahl)](https://codecov.io/gh/facebookexperimental/MIRAI) [![deps.rs](https://deps.rs/repo/github/facebookexperimental/MIRAI/status.svg)](https://deps.rs/repo/github/facebookexperimental/MIRAI)
MIRAI is an abstract interpreter for the [Rust](https://www.rust-lang.org/) compiler's [mid-level intermediate
representation](https://github.com/rust-lang/rfcs/blob/master/text/1211-mir.md) (MIR).
It is intended to become a widely used static analysis tool for Rust.

## Using MIRAI

You'll need to install MIRAI as described here for [MacOS and Windows](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/InstallationGuide.md)
and here for [Linux](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/Linux.md).

To run MIRAI, use cargo with `RUSTC_WRAPPER` set to `mirai`.
Use `rustup override set nightly-YYYY-MM-DD` to make Cargo use the same version of Rust as MIRAI. See the above installation
instruction to determine which version to use. If you forget to do that or use the wrong version,
you'll see an error message complaining about a dynamic load library not being found.

The easiest way to get started is to first build your project in the normal way (with one exception:
 set `RUSTFLAGS="-Z always_encode_mir"` to force the rust compiler to include MIR into its compiled output).
Refer to [this link](https://doc.rust-lang.org/1.30.0/book/2018-edition/ch01-00-getting-started.html) for details
on compiling a cargo project.
When there are no compile errors,
no lint errors and no test failures, you can proceed to the next step and run MIRAI. For example:
```
touch src/lib.rs
RUSTFLAGS="-Z always_encode_mir" RUSTC_WRAPPER=mirai cargo build
```

The touch command (which needs to reference a real file in your project) forces Cargo to re-run rustc and to not assume
that its cached error messages are still correct.

This will likely produce some warnings, which you can then fix by adding annotations declared in this
[crate](https://crates.io/crates/mirai-annotations). Keep re-touching and running cargo build as above until
there are no more warnings.

At this stage your code will be better documented and more readable. Perhaps you'll also have found and fixed a few bugs.

You can use the environment variable `MIRAI_FLAGS` to get cargo to provide command line options to MIRAI. The value is a
string which can contain any of the following flags:

- `--test_only`: instructs MIRAI to analyze only test methods in your crate. You must also provide the `--tests`
  option to the `cargo build` command to include those tests actually into your build.
- `--diag=default|verify|library|paranoid`: configures level of diagnostics. With `default` MIRAI
   will not report errors which are potential 'false positives'. With `verify` it will point out
   functions that may contain such errors. With `library` it will require explicit preconditions.
   With `paranoid` it will flag any issue that may be an error.
- `--single_func <name>`: the name of a specific function you want to analyze.
- `--body_analysis_timeout <seconds>`: the maximum number of seconds to spend analyzing a function body.
- `--call_graph_config <path_to_config>`: path to configuration file for call graph generator (see [Call Graph Generator documentation](documentation/CallGraph.md)). No call graph will be generated if this is not specified.
- `--`: any arguments after this marker are passed on to rustc.

You can get some insight into the inner workings of MIRAI by setting the verbosity level of log output to one of 
`warn`, `info`, `debug`, or `trace`, via the environment variable `MIRAI_LOG`.

## Using MIRAI together with the Rust design by contracts crate

Support for MIRAI is available in the [design by contracts crate](https://gitlab.com/karroffel/contracts).
See the [shopping cart example](https://github.com/facebookexperimental/MIRAI/blob/master/examples/shopping_cart/src/main.rs) for usage.

## Developing MIRAI
See the [developer guide](https://github.com/facebookexperimental/MIRAI/blob/master/documentation//DeveloperGuide.md)
for instructions on how to build, run and debug MIRAI.

## Full documentation
* [Overview of project](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/Overview.md).
* [Architecture](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/Architecture.md).
* [Design discussions](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/DesignDiscussions.md).
* [Further reading](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/FurtherReading.md).

## Road map
* Stabilize MIRAI and get rid of crashing bugs.
* Summaries for intrinsics and standard library functions without MIR.

## Join the MIRAI community
<!-- * Website:
* Facebook page:
* Mailing list
* irc:  -->
See the [CONTRIBUTING](https://github.com/facebookexperimental/MIRAI/blob/master/CONTRIBUTING.md) file for how to help out.

## License
MIRAI is MIT licensed, as found in the [LICENSE](https://github.com/facebookexperimental/MIRAI/blob/master/LICENSE) file.
