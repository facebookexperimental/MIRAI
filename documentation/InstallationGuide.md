# Installation Guide

In order to use MIRAI, you need to install Rust, install Z3, and install MIRAI into cargo.

## Linux is not supported

Sadly, on Linux, the Rust compiler is built in a way that precludes MIRAI from working. The core issue seems to be
the way the C++ standard library is statically linked into the LLVM bundled with Rust. This breaks the Z3 SMT solver
that MIRAI depends on. Even when using a custom build of the Rust compiler, in which static linking is not enabled,
there are problems with the Rust bindings for Z3 that prevents MIRAI from compiling.

## Installing Rust

You should install rustup and then use it to get hold of the latest Rust compiler.
See [here](https://doc.rust-lang.org/book/ch01-01-installation.html) for instructions.

Mirai depends on unstable private APIs of the rust compiler to do things like parsing, type checking and
lowering to MIR. These can only be accessed by using the nightly build of the compiler. So use rustup to set
the (last known good) nightly build as the default for the mirai project.

```rustup override set nightly-2019-MM-DD```

The source of truth for the last known good nightly is .travis.yml.

You can also check [here](https://rust-lang.github.io/rustup-components-history/index.html) to find a later build than
that. If cargo, clippy, miri or rustfmt is not working, the build is not good for MIRAI. Even then, if there has been a
breaking change to the API, MIRAI might not build. If this blocks you file an issue on GitHub and
the matter will be resolved promptly.

## Installing Z3

The simplest way to install Z3 on a system with brew is just
```
brew install z3
```

Alternatively, you can find pre-built binaries for Z3 [here](https://github.com/Z3Prover/z3/releases). There are also binary libraries
for macOS and Windows included in the binaries directory of MIRAI.

For macOS, the binary will have to be placed somewhere where it can be 
found and dynamically loaded by the Rust runtime. This can be done by copying the binary into `/usr/local/lib`.

```
cp binaries/libz3.dylib /usr/local/lib
```

For Windows, the binary does not have to be moved.

## Installing MIRAI into cargo

If you just want to use MIRAI you can simply do:
```
cargo install --git https://github.com/facebookexperimental/MIRAI --force --version 1.0.1 mirai
```

If you want to help develop MIRAI see the [developer guide](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/DeveloperGuide.md)
