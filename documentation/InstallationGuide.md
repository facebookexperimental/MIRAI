# Installation Guide

In order to use MIRAI, you need to install Rust and then install MIRAI into cargo.

## Installing Dependencies

Please ensure that all of the following dependencies are installed:

-  Rust using rustup. You can find the installation instructions [here](https://doc.rust-lang.org/book/ch01-01-installation.html).
- Cmake. The installation instructions can be found [here](https://cmake.org/install/).
- Clang. The installation instructions can be followed [here](https://clang.llvm.org/get_started.html).

## Installing MIRAI into cargo

The best way to install MIRAI into cargo is to clone the MIRAI repository:

```bash
git clone https://github.com/facebookexperimental/MIRAI.git
cd MIRAI
```

Then build and install MIRAI into cargo:

```bash
cargo install --locked --path ./checker
```

## Contributing to MIRAI

If you want to help develop MIRAI see
the [developer guide](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/DeveloperGuide.md)
