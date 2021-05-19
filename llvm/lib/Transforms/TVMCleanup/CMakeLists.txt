file(GLOB_RECURSE SRCS *.cpp)

add_llvm_library(TVMCleanup MODULE BUILDTREE_ONLY
  ${SRCS}
  DEPENDS
  intrinsics_gen
  PLUGIN_TOOL
  opt)

target_link_libraries(TVMCleanup
  PRIVATE
  $ENV{SS_TOOLS}/lib/libdsa.so)


target_include_directories(TVMCleanup
  PRIVATE
  $ENV{SS_TOOLS}/include)
