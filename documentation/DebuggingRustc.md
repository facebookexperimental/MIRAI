# Debugging Rustc

Since Mirai makes use of a private and unstable API with sparse documentation, it can be very helpful to debug
Mirai while seeing the actual rustc sources in the debugger. By default, this does not happen.

To work around this some painful steps need to be taken. First of all, get the sources of rustc and build them.

```
# cd to the directory where you want to keep the rust compiler sources
git clone https://github.com/rust-lang/rust/ rustc
cd rustc
cp config.toml.example config.toml
# Now edit config.toml and set debug, debug-assertions, debuginfo, and debuginfo-lines to true
./x.py build src/rustc
# You may have to change the architecture in the next command
rustup toolchain link custom build/nightly-x86_64-apple-darwin/stage2
```

If you have done the above previously, be sure to pull down the latest changes from the github repo.

Next build the Mirai sources.

```
# cd to your mirai directory
rustup override set custom
cargo clean
cargo build
```

Now switch back to using the nightly build, or the Rust Language Service (RLS) will crash when you try to load VSCode or 
Clion.

```
rustup override set nightly
```

Now close and reload VSCode (Clion does not support this scenario) and modify the configuration to reference the custom 
build of rustc

```    {
        "type": "lldb",
        "request": "launch",
        "name": "Debug executable 'mirai'",
        "cargo": {
            "args": [
                "build",
                "--bin=mirai",
                "--package=Mirai"
            ],
            "filter": {
                "kind": "bin"
            }
        },
        "env": {
           "DYLD_LIBRARY_PATH": "${env:HOME}/.rustup/toolchains/custom/lib",
        },
        "sourceLanguages": ["rust"],
        "args": [<what you'll give to rustc, split into an array of strings using space as the delimiter>],
        "cwd": "${workspaceFolder}/checker",
    },
```

Now switch back to the custom build, otherwise mirai wont load.

```
rustup override set custom
```

And now you can finally debug while seeing rustc sources. Be aware, however, that doing anything in the editor that
invokes the RLS will cause it to crash, which sooner or later causes all sorts of trouble.

When you are done debugging, revert to the nightly build.