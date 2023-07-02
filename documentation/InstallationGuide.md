# Installation Guide

In order to use MIRAI, you need to install Rust and then install MIRAI into cargo.

## Installing Rust

You should install Rust using rustup. See [here](https://doc.rust-lang.org/book/ch01-01-installation.html)
for instructions.

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

If a build error occurs, you need to execute the folloing command to install dependencies.

```bash
sudo apt install cmake clang libclang-dev
```

## Contributing to MIRAI

If you want to help develop MIRAI see
the [developer guide](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/DeveloperGuide.md)
