add_library(schnorrsig INTERFACE)
target_include_directories(schnorrsig INTERFACE ${secp256k1_SOURCE_DIR})

if (use_benchmark)
  add_executable(bench_schnorrsig
    ${secp256k1_SOURCE_DIR}/src/bench_schnorrsig.c)
  target_link_libraries(bench_schnorrsig PRIVATE secp256k1 schnorrsig)
endif()
