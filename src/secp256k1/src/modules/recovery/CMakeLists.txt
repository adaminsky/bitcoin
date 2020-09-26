add_library(recovery INTERFACE)
target_include_directories(recovery INTERFACE ${secp256k1_SOURCE_DIR})

if (use_benchmark)
  add_executable(bench_recover ${secp256k1_SOURCE_DIR}/src/bench_recover.c)
  target_link_libraries(bench_recover PRIVATE secp256k1 recovery)
endif()
