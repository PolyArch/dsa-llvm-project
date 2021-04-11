file(GLOB_RECURSE SRCS *.cpp)

add_llvm_library(DSAFusion MODULE BUILDTREE_ONLY
  ${SRCS}
  DEPENDS
  intrinsics_gen
  PLUGIN_TOOL
  opt)

target_link_libraries(DSAFusion
  PRIVATE
  $ENV{SS_TOOLS}/lib/libdsa.so)


target_include_directories(DSAFusion
  PRIVATE
  $ENV{SS_TOOLS}/include)