mkdir build-debug
cd build-debug

cmake -G "Unix Makefiles" \
-DLLVM_TARGETS_TO_BUILD="X86" \
-DLLVM_EXPERIMENTAL_TARGETS_TO_BUILD="RISCV" \
-DLLVM_ENABLE_PROJECTS="clang;libunwind;lld;openmp" \
-DCMAKE_BUILD_TYPE=Debug \
-DCMAKE_INSTALL_PREFIX=../install-debug \
-DLLVM_BINUTILS_INCDIR=$GEM_FORGE_TOP/lib/binutils/include \
-DBUILD_SHARED_LIBS=ON \
-DOPENMP_ENABLE_LIBOMPTARGET=OFF \
../llvm \

make install -j $CORES
cd ..

mkdir build-release
cd build-release
cmake -G "Unix Makefiles" \
-DLLVM_TARGETS_TO_BUILD="X86" \
-DLLVM_EXPERIMENTAL_TARGETS_TO_BUILD="RISCV" \
-DLLVM_ENABLE_PROJECTS="clang;libunwind;lld;openmp" \
-DCMAKE_BUILD_TYPE=Release \
-DCMAKE_INSTALL_PREFIX=../install-release \
-DLLVM_BINUTILS_INCDIR=$GEM_FORGE_TOP/lib/binutils/include \
-DBUILD_SHARED_LIBS=ON \
-DOPENMP_ENABLE_LIBOMPTARGET=OFF \
../llvm \

make install -j $CORES
cd ..

mkdir build-omp-x86-static
cd build-omp-x86-static
cmake \
-DCMAKE_BUILD_TYPE=Release \
-DCMAKE_INSTALL_PREFIX=../install-release \
-DLIBOMP_ENABLE_SHARED=False \
-DOPENMP_ENABLE_LIBOMPTARGET=OFF \
../openmp \

make install -j $CORES
cd ..
