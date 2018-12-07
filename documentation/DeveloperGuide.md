# Developer Guide

The instructions assume that you've cloned the mirai repository into your home directory.

## Building

You'll need to have Rust installed on your system. See 
[here](https://doc.rust-lang.org/book/2018-edition/ch01-01-installation.html) for instructions.

Mirai depends on unstable private APIs of the rust compiler to do things like parsing, type checking and
lowering to MIR. These can only be accessed by using the nightly build of the compiler. So use rustup to set
the nightly build as the default for the mirai project.

```rustup override set nightly```

That done, all you need to do to build Mirai is to type `cargo build` in your command shell. Generally building happens 
automatically as you run tests.


## Editing

The best editing experience seems to be with [Clion](https://www.jetbrains.com/clion/). 

Alternatively there is also
[VSCode](https://code.visualstudio.com/). You'll want to install these extensions: 
[Rust (rls)](https://github.com/rust-lang-nursery/rls-vscode), [CodeLLDB](https://github.com/vadimcn/vscode-lldb) and
[Better TOML](https://github.com/bungcip/better-toml).

There is also [Nuclide](https://nuclide.io/). You'll want to install the [Rust](https://atom.io/packages/language-rust)
extension. This option is pretty basic and not recommended right now. It does have a better integration with Git, so I
actually use Clion for editing, VSCode for debugging and Nuclide for doing source control.

## Running

Running `cargo build` will produce a binary at `target/debug/mirai`. Create a handy alias for the binary with

`alias mirai="DYLD_LIBRARY_PATH=~/.rustup/toolchains/nightly-x86_64-apple-darwin/lib ~/mirai/target/debug/mirai"`

Afterward, you can run the mirai binary as if it were rustc.
 
To run mirai via cargo, first do `cargo install --force --path  ~/mirai` then set the `RUSTC_WRAPPER` environment
variable to `mirai`. Note that Cargo takes care of the library path so the alias is not needed unless you want
to run mirai directly. 

## Debugging

VSCode gives a better experience than Clion at the moment. To use VSCode you'll need to add the following to the
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
        "args": [<what you'll give to rustc, split into an array of strings using space as the delimiter>],
        "cwd": "${workspaceFolder}",
    },
```

Since Mirai makes use of a private and unstable API with sparse documentation, it can be very helpful to debug
Mirai while seeing the actual rustc sources in the debugger. By default, this does not happen. To make it happen, see 
[debugging](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/DebuggingRustc.md) with Rustc 
sources.

## Testing

Testing is done via `cargo test`. We favor integration tests over unit tests and require every pull request to have 100%
test coverage. The code coverage tool (`cargo tarpaulin`) is still buggy, so this may not always be possible, but all
exceptions should be called out and explained in the pull request test plan.

For the time being (see issue #10), we provide a separate test method in integration_tests.rs for each test input in
the [tests/run-pass](https://github.com/facebookexperimental/MIRAI/blob/master/tests/run-pass) directory.
