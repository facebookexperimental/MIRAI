# Developer Guide

The instructions assume that you've cloned the mirai repository into your home directory.

## Obtaining the MIRAI sources

You'll need a recent version of the Rust compiler and you'll need to clone the MIRAI source repository.
See [here](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/InstallationGuide.md) for more detailed instructions.


## Editing

The best editing experience seems to be with [Clion](https://www.jetbrains.com/clion/). 

Alternatively there is also
[VSCode](https://code.visualstudio.com/). You'll want to install these extensions: 
[Rust (rls)](https://github.com/rust-lang-nursery/rls-vscode), [CodeLLDB](https://github.com/vadimcn/vscode-lldb) and
[Better TOML](https://github.com/bungcip/better-toml).


## Running

Running `cargo build` will produce a binary at `target/debug/mirai`.
 
Unfortunately cargo build sets the dynamic library load path (rpath) that is linked into the binary to a path that is
invalid when the binary is run. If you run the binary via cargo `cargo run -- <args>` then cargo overrides the bad
rpath by providing the correct path in the environment variable `DYLD_LIBRARY_PATH`.
 
If you run without using cargo, you'll need to set the variable yourself, or you can create a handy alias for the binary
with

`alias mirai="DYLD_LIBRARY_PATH=$(rustc --print sysroot)/lib ~/mirai/target/debug/mirai"`

You can then run mirai as if it were rustc, because it is in fact rustc, just with an added plug in.
 
To run mirai via cargo, as if it were rustc, first do `cargo install --force --path  ~/mirai` then set the
`RUSTC_WRAPPER` environment variable to `mirai`.

## Debugging

### Clion

To debug MIRAI with CLion, edit the default configuration to provide some more information. For example here is
my configuration for debugging a particular test case:

```
run --package mirai --bin mirai -- tests/run-pass/assume.rs 
  --extern mirai_annotations=/Users/hermanv/projects/mirai/target/debug/deps/libmirai_annotations-1badff3b9dc95bd4.rlib
```

The `--extern` option is necessary for the Rust compiler to find the mirai_annotations library that is used to provide
the assume and verify macros used in the test case. This is pretty annoying and to make matters even worse, the
compiler complains if the compiler used to compile the annotations library does not match the compiler that is
hosting MIRAI, so you have to update this frequently. If you have trouble identifying the matching version, just do
cargo clean and then cargo build and look in the newly constructed target/debug/deps directory.

You'll also have to set some environmental variables, for example:
```
DYLD_LIBRARY_PATH=/Users/hermanv/.rustup/toolchains/nightly-x86_64-apple-darwin/lib;
MIRAI_LOG=debug
```

DYLD_LIBRARY_PATH allows the loader to find the rust runtime library. You need to set it explicitly because the path
provided by cargo to the Rust compiler is a temporary one, so the path that ends up in the binary being debugged does
not work.

MIRAI_LOG allows you to set the logging level. Since the rust debugger does not allow you to see non primitive values,
you'll have to sprinkle you code with lots of log statements.

Finally, set the working directory to the checker directory, i.e. something like `/Users/hermanv/mirai/checker`.

### VsCode

To use VSCode you'll need to add the following to the
configurations property of the content of the launch.json file in the .vscode directory of your project directory:
```    {
        "type": "lldb",
        "request": "launch",
        "name": "Debug executable 'mirai'",
        "cargo": {
            "args": [
                "build",
                "--bin=mirai",
                "--package=mirai"
            ],
            "filter": {
                "kind": "bin"
            }
        },
        "env": {
           "DYLD_LIBRARY_PATH": "${env:HOME}/.rustup/toolchains/nightly-x86_64-apple-darwin/lib",
        },
        "sourceLanguages": ["rust"],
        "args": [<what you'll give to rustc, split into an array of strings using space as the delimiter,
        remember to append the --extern option described in the CLion section>],
        "cwd": "${workspaceFolder}/checker",
    },
```

Note that VSCode runs cargo to build mirai (if necessary) and gets the location of the binary from cargo. When
actually debugging, however, it runs the binary directly, so it is necessary to set DYLD_LIBRARY_PATH. VSCode config
files don't support things like `$(rustc --print sysroot)`, hence the more brittle expression above.

## Debugging the test framework

If you are tweaking the test framework and need to debug your tweaks, you'll need a different configuration.

### Clion

Use this configuration:
```
test --package mirai --test integration_tests ""
```

### VsCode

There does not seem to be a way to do this with a cargo configuration, so I first use cargo test to get the name of
the generated binary and then debug that using a launch configuration along these lines:
```
{
            "type": "lldb",
            "request": "launch",
            "name": "Launch",
            "program": "${workspaceFolder}/target/debug/deps/integration_tests-0ca00d8d322a6adc",
            "sourceLanguages": ["rust"],
            "args": [],
            "cwd": "${workspaceFolder}/checker",
            "env": {
                "DYLD_LIBRARY_PATH": "${env:HOME}/.rustup/toolchains/nightly-x86_64-apple-darwin/lib",
                "MIRAI_LOG": "debug",
            }
        },        
```

## Debugging MIRAI analyzing MIRAI

### Clion

MIRAI has a lot of dependencies and all of these need to be specified explicitly when running mirai directly (i.e. not 
via cargo). The way I do this is to first run "cargo clean -p mirai; cargo build -v" and then to copy and past all of
the parameters given to rustc by cargo to the first configuration described above, replacing everything following the
 `-- `option.

### VsCode

I don't use VsCode for this scenario. You'll probably want to write a script to parse the rustc command line and dump
it into the JSON format needed by VSCode.

## Debugging rustc

Since Mirai makes use of a private and unstable API with sparse documentation, it can be very helpful to debug
Mirai while seeing the actual rustc sources in the debugger. By default, this does not happen. To make it happen, see 
[debugging](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/DebuggingRustc.md) with Rustc 
sources.

## Testing

Testing is done via `cargo test`. We favor integration tests over unit tests and require every pull request to have 100%
test coverage.

Before putting up a pull request it is also advisable to run the 'validate.sh' script. This will ensure that the code
is properly formatted and that Clippy is happy. It also runs MIRAI on itself, which is a kind of stress test.