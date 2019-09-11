# Installation Guide for Linux

In order to use MIRAI, you need to install Rust, install Z3, and install MIRAI into cargo.

## Installing Rust

You should install rustup and then use it to get hold of the latest Rust compiler.
See [here](https://doc.rust-lang.org/book/ch01-01-installation.html) for instructions.

## Installing Z3

On Fedora install it with
```
dnf install z3-devel
```

If that works, you're done. If not, you can find pre-built binaries for Z3 
[here](https://github.com/Z3Prover/z3/releases). There are also binary libraries
for linux included in the binaries directory of MIRAI.

Alternatively you'll have to build the Z3 binaries yourself, 
as described [here](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/Z3AndLinux.md).

## Installing MIRAI into cargo

On Linux the z3 library has to be statically linked into the mirai executable. The best way to do that is
clone the MIRAI repository:

```
git clone https://github.com/facebookexperimental/MIRAI.git
cd MIRAI
```

If you want a particular version of MIRAI, checkout the corresponding tag.
```
git fetch origin
git checkout tags/v1.0.3
```

If you rebuilt the Z3 binaries yourself, copy it to the `./binaries` directory.

Then build and install MIRAI into cargo, using the RUSTFLAGS variable to tell the linker where to find z3.

```
RUSTFLAGS='-Clink-arg=-L./binaries -Clink-arg=-lstdc++' cargo install  --path ./checker
```

## Contributing to MIRAI

If you want to help develop MIRAI see the [developer guide](https://github.com/facebookexperimental/MIRAI/blob/master/documentation/DeveloperGuide.md)
