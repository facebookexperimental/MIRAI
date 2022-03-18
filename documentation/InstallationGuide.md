# Installation Guide for MacOs and Windows

In order to use MIRAI, you need to install Rust, install Z3, and install MIRAI into cargo.

## Installing Rust

You should install Rust using rustup. See [here](https://doc.rust-lang.org/book/ch01-01-installation.html)
for instructions.

## Installing Z3

The simplest way to install Z3 on a (non linux) system with brew is just

```
brew install z3
```

For macOS the binary will have to be placed somewhere where it can be found and dynamically loaded by the Rust runtime.

```
cp binaries/libz3.dylib /usr/local/lib
```

## Installing MIRAI into cargo

The best way to install MIRAI into cargo is to clone the MIRAI repository:

```
git clone https://github.com/facebookexperimental/MIRAI.git
cd MIRAI
```

Next, make sure that the correct version of rustc is installed, along with some optional components

```
./setup.sh
```

Then build and install MIRAI into cargo:

```
cargo install --locked --path ./checker
```

## Contributing to MIRAI

If you want to help develop MIRAI see
the [developer guide](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/DeveloperGuide.md)
