# Installation Guide

In order to use MIRAI, you need to install Rust, install MIRAI into cargo, and install Z3.

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
that. If there is a breaking change to the API, MIRAI might not build. If this blocks you file an issue on GitHub and
the matter will be resolved promptly.

## Building MIRAI

Clone the MIRAI source repository into your home directory and build it:

```
cd ~
git clone git@github.com:facebookexperimental/MIRAI.git
```

## Install MIRAI into cargo

You'll need to change the nightly version below to the one found in .travis.yml. The install command will also
build MIRAI.

```
cd ~/MIRAI
rustup override set nightly-2019-MM-DD
cargo install --path ./checker
```

## Installing Z3

You can find pre-built binaries for Z3 [here](https://github.com/Z3Prover/z3/releases). There are also binary libraries
for macOS and Windows included in the binaries directory of MIRAI.

For Windows, the binary does not have to be moved. For macOS, the binary will have to be placed somewhere where it can be 
found and dynamically loaded by the Rust runtime. This can be done by copying the binary into `/usr/local/lib`.

```
cp binaries/libz3.dylib /usr/local/lib
```


