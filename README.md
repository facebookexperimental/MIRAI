# MIRAI [![codecov](https://codecov.io/gh/facebookexperimental/MIRAI/branch/main/graph/badge.svg?token=q4jzL09Ahl)](https://codecov.io/gh/facebookexperimental/MIRAI) [![deps.rs](https://deps.rs/repo/github/facebookexperimental/MIRAI/status.svg)](https://deps.rs/repo/github/facebookexperimental/MIRAI)
MIRAI is an abstract interpreter for the [Rust](https://www.rust-lang.org/) compiler's [mid-level intermediate
representation](https://github.com/rust-lang/rfcs/blob/master/text/1211-mir.md) (MIR).
It is intended to become a widely used static analysis tool for Rust.

## Who should use MIRAI

MIRAI can be used as a linter that finds panics that may be unintentional or are not the best way to terminate a
program. This use case generally requires no annotations and is best realized by integrating MIRAI into a CI pipeline.

MIRAI can also be used to verify correctness properties. Such properties need to be encoded into annotations of the
source program.

A related use is to better document an API via explicit precondition annotations and then use MIRAI to check that 
the annotations match the code.

Finally, MIRAI can be used to look for security bugs via taint analysis (information leaks, code injection bugs, etc.)
and constant time analysis (information leaks via side channels). Unintentional (or ill-considered) panics can also
become security problems (denial of service, undefined behavior).

## How to use MIRAI

You'll need to install MIRAI as described 
[here](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/InstallationGuide.md).

Then use `cargo mirai` to run MIRAI over your current package. This works much like `cargo check` but uses MIRAI rather
than rustc to analyze the targets of your current package.

This will likely produce some warnings. Some of these will be real issues (true positives) that you'll fix by changing
the offending code. Other warnings will be due to limitations of MIRAI and you can silence them by adding annotations
declared in this [crate](https://crates.io/crates/mirai-annotations).

Once MIRAI gives your code a clean bill of health, your code will be better documented and more readable. Perhaps you'll 
also have found and fixed a few bugs.

You can use the environment variable `MIRAI_FLAGS` to get cargo to provide command line options to MIRAI. The value is a
string which can contain any of the following flags:

- `--diag=default|verify|library|paranoid`: configures level of diagnostics. With `default` MIRAI
   will not report errors which are potential 'false positives'. With `verify` it will point out
   functions that may contain such errors. With `library` it will require explicit preconditions.
   With `paranoid` it will flag any issue that may be an error.
- `--single_func <name>`: the name of a specific function you want to analyze.
- `--body_analysis_timeout <seconds>`: the maximum number of seconds to spend analyzing a function body.
- `--call_graph_config <path_to_config>`: path to configuration file for call graph generator (see [Call Graph Generator documentation](documentation/CallGraph.md)). No call graph will be generated if this is not specified.
- `--print_function_names`: just print the source location and fully qualified function signature of every function.
- `--`: any arguments after this marker are passed on to rustc.

You can get some insight into the inner workings of MIRAI by setting the verbosity level of log output to one of 
`warn`, `info`, `debug`, or `trace`, via the environment variable `MIRAI_LOG`.

## Developing MIRAI
See the [developer guide](https://github.com/facebookexperimental/MIRAI/blob/main/documentation//DeveloperGuide.md)
for instructions on how to build, run and debug MIRAI.

## Full documentation
* [Overview of project](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/Overview.md).
* [Architecture](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/Architecture.md).
* [Design discussions](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/DesignDiscussions.md).
* [Further reading](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/FurtherReading.md).

## Join the MIRAI community
<!-- * Website:
* Facebook page:
* Mailing list
* irc:  -->
See the [CONTRIBUTING](https://github.com/facebookexperimental/MIRAI/blob/main/CONTRIBUTING.md) file for how to help out.

## License
MIRAI is MIT licensed, as found in the [LICENSE](https://github.com/facebookexperimental/MIRAI/blob/main/LICENSE) file.
