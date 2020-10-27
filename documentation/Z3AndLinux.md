# Building and installing Z3 on Linux

On Linux, Z3 must be linked statically into MIRAI, otherwise there'll be a conflict between MIRAI and the rust compiler.

The statically linked library that comes from the [prebuilt Z3 distributions](https://github.com/Z3Prover/z3/releases)
does not work for MIRAI. To fix that the library must be using the PIC format.

To obtain such binary (if the one provided in the binaries directory does not work for you, or you are the poor soul
who has to update the binaries directory), do the following:

Clone the Z3 source repository (preferably into the directory containing the MIRAI clone):
```
git clone https://github.com/Z3Prover/z3.git
```

Then do:
```
mkdir build
cd build
cmake -DCMAKE_BUILD_TYPE=Release -DZ3_BUILD_LIBZ3_SHARED=FALSE ../
# use the number of jobs that makes sense for your machine
make -j32
```

The libz3.a library in build will now be suitable for linking into MIRAI. Copy it to the binaries directory
(or fix RUSTFLAGS appropriately).
