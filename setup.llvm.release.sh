cmake -G "Ninja" \
-DLLVM_TARGETS_TO_BUILD="X86" \
-DLLVM_EXPERIMENTAL_TARGETS_TO_BUILD="RISCV" \
-DLLVM_ENABLE_PROJECTS="clang;libunwind;lld;openmp" \
-DCMAKE_BUILD_TYPE=Release \
-DCMAKE_INSTALL_PREFIX=../install-release \
-DLLVM_BINUTILS_INCDIR=~/Documents/binutils/include \
-DBUILD_SHARED_LIBS=ON \
../llvm \

