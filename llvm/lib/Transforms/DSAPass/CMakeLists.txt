file(GLOB_RECURSE SRCS *.cpp)

add_llvm_library(DSAPass MODULE BUILDTREE_ONLY
  ${SRCS}
  DEPENDS
  intrinsics_gen
  PLUGIN_TOOL
  opt)

target_link_libraries(DSAPass PRIVATE $ENV{SS_TOOLS}/lib/libdsa.so)

target_include_directories(DSAPass PRIVATE $ENV{SS_TOOLS}/include)

target_compile_definitions(DSAPass PUBLIC ENABLE_LLVM)
