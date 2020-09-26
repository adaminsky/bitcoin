add_library(ecdh INTERFACE)
target_include_directories(ecdh INTERFACE ${secp256k1_SOURCE_DIR})
target_include_directories(ecdh INTERFACE ${secp256k1_SOURCE_DIR}/src)

if (use_benchmark)
  add_executable(bench_ecdh ${secp256k1_SOURCE_DIR}/src/bench_ecdh.c)
  target_link_libraries(bench_ecdh ecdh secp256k1)
endif()
