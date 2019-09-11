# Installation Guide for MacOs and Windows

In order to use MIRAI, you need to install Rust, install Z3, and install MIRAI into cargo.

## Installing Rust

You should install rustup and then use it to get hold of the latest Rust compiler.
See [here](https://doc.rust-lang.org/book/ch01-01-installation.html) for instructions.

## Installing Z3

The simplest way to install Z3 on a (non linux) system with brew is just
```
brew install z3
```

On Linux (Fedora) install it with
```
dnf install z3-devel
```

If that works, you're done. If not, you can find pre-built binaries for Z3 
[here](https://github.com/Z3Prover/z3/releases). There are also binary libraries
for linux, macOS and Windows included in the binaries directory of MIRAI.

For macOS and Windows, the binary will have to be placed somewhere where it can be 
found and dynamically loaded by the Rust runtime. 

For macOs this can be done by copying the binary into `/usr/local/lib`.

```
cp binaries/libz3.dylib /usr/local/lib
```

For Windows, this can be done by copying the binary into `System32`.

```
copy binaries\libz3.dll %SYSTEM32%
```

Alternatively copy it into the same directory where the MIRAI executable has been placed. To find the directory use the
where command. For example:

```
where /r c:\ mirai.exe 
```

## Installing MIRAI into cargo

If you just want to use MIRAI you can simply do:
```
cargo install --git https://github.com/facebookexperimental/MIRAI --force --version 1.0.3 mirai
```

## Contributing to MIRAI

If you want to help develop MIRAI see the [developer guide](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/DeveloperGuide.md)
