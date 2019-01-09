The Stream-Specialized LLVM Compiler Infrastructure
===================================================

LLVM compiler infrastructure for stream-specialzed architecture family.
This repo is intended to be a part of [ss-stack](https://github.com/polyarch/ss-stack).
Customized gnu-riscv-toolchain and gem5 simulator are requied to assemble and run
the binary.

Installation
------------

Stream-specialized architectures are all RISCV ISA based, so cross-platform
compilation is required. Thus, the compilation options are slightly different.

```sh
$ git clone --recursive [this repo]
$ cd /path/to/this/repo; mkdir build; cd build
$ cmake -G "Unix Makefiles" -DCMAKE_BUILD_TYPE="Debug" \
  -DBUILD_SHARED_LIBS=True -DLLVM_USE_SPLIT_DWARF=True \
  -DLLVM_OPTIMIZED_TABLEGEN=True -DLLVM_BUILD_TESTS=False \
  -DDEFAULT_SYSROOT="$(SS_TOOLS)/riscv64-unknown-elf" \
  -DGCC_INSTALL_PREFIX="$(SS_TOOLS)" \
  -DLLVM_DEFAULT_TARGET_TRIPLE="riscv64-unknown-elf" \
  -DLLVM_EXPERIMENTAL_TARGETS_TO_BUILD="RISCV" ..
$ make -j9
```

Hollo world!
------------
It is a little bit tricky to build RISCV binaries with the current LLVM toolchain:
LLVM toolchain so far can only generate codes, but linking is not perfectly supported
yet. Thus, we need to borrow linker from the gnu toolchain.

Clang can only, by default, generate hard-float (floats goes to its specialized
register file) programs, and GNU toolchain, by default, is built with soft-float
library. This may cause an ABI mismatch. Thus, we need to add `--enable-multilib`
when configuring GNU-RISCV build.

Because RISCV is not the native host ISA, when compiling with Clang, `--sysroot` should
be specified to support C/C++ standard libraries.


```C
// main.c
#include <stdio.h>
int main() {
  puts("Hello world!\n");
  return 0;
}
```

```sh
$ clang main.c -O -c --sysroot=/where/riscv/gnu/toolchain/installed
$ riscv-gnu-unknown-elf-gcc main.o -o main -march=rv64imac -mabi=lp64
# Using RISCV emulator or simulator to verify the binary
```

Try an example
--------------

Examples are available in `examples/StreamSpecialize`:
`Tests` is functional test of each feature of the compiler supported.
`ToDo` is the features not supported yet.
`CtrlFlow` is the functional test require `BACKCGRA=1` environment variable.
`Dsp/PolyBench` are the corresponding application domain.

You can `cd` to any directory, and run the examples by simply typing the following
shell commands:
```sh
$ ./run.sh # which runs all the workloads in this folder
$ ./run.sh opt-ss-[appname].out # which runs the corresponding application
```

To better understand the second way of running, here is an example.
Say, we have `Tests/vecadd.cc`, so we can type
```sh
$ cd Tests
$ ./run.sh opt-ss-vecadd.out
```

Then, prefix `opt-ss-` is required because of the toolchain usage:
In general, the compilation pipeline is something like this
(Refer `Common/Makefile.inc` for more details):
```sh
# Generate llvm assembly code
$ clang vecadd.cc -emit-llvm -c [some other flags]

# Extract DFGs, and encode data streams
# "ss-" prefix indicates already transformed for stream specialization
$ opt -load path/to/StreamSpecialize.so < vecadd.bc > ss-vecadd.bc

# General optimization to clean up
# "opt-" prefix indicates optimized and ready for code gneration
$ opt -O3 < ss-vecadd.bc > opt-ss-vecadd.bc

# Code generation, assume our host RISCV core has all the modules
# of RISCV ISA enabled
# I am not sure how to change `llc` ABI so that we can build gnu-riscv
# without multilib enabled.
$ llc -mattr+m,+f,+a,+c opt-ss-vecadd.bc

# Link and assemble binary
$ riscv-unknown-elf-g++ opt-ss-vecadd.s -o opt-ss-vecadd.out \
      -march=rv64imac -abi=lp64 -lm
```

For all the intermediate `xxx.bc`, we can all use `make xxx.ll` to dump
the text format to debug and sanity check.
