# Installation Guide for Linux

In order to use MIRAI, you need to install Rust, install Z3, and install MIRAI into cargo.

## Installing Rust

You should install Rust using rustup. See [here](https://doc.rust-lang.org/book/ch01-01-installation.html)
for instructions.

## Installing Z3

On Fedora install it with

```
dnf install z3-devel
```

On Ubuntu install it with

```
sudo apt-get install libz3-dev
```

If you are using a distribution other than Fedora or Ubuntu and neither of the options above are available to you,
you'll have to figure out for yourself how to install Z3. This [link](https://github.com/Z3Prover/z3) would be good
place to start looking for help.

If you figure things out, please submit a pull request to update this page.

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

On Fedora, z3-sys is currently unable to find the `z3.h` header file, so you may need to specify the path to it as
follows:

```
CPATH=/usr/include/z3 cargo install --locked --path ./checker
```

## Contributing to MIRAI

If you want to help develop MIRAI see
the [developer guide](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/DeveloperGuide.md)
