find_package(OpenSSL REQUIRED)

add_executable(gen_context gen_context.c)
target_include_directories(gen_context PRIVATE ${libsecp256k1_SOURCE_DIR})
add_custom_command(
  OUTPUT ecmult_static_context.h
  COMMAND gen_context
  WORKING_DIRECTORY ${libsecp256k1_SOURCE_DIR}
  DEPENDS gen_context)

set(HEADER_LIST ${libsecp256k1_SOURCE_DIR}/include/secp256k1.h
  ${libsecp256k1_SOURCE_DIR}/include/secp256k1_preallocated.h)

add_library(secp256k1 secp256k1.c ${HEADER_LIST} ecmult_static_context.h)
target_include_directories(secp256k1
  PUBLIC ${libsecp256k1_SOURCE_DIR} ${libsecp256k1_SOURCE_DIR}/src
  INTERFACE ${libsecp256k1_SOURCE_DIR}/include)

if (set_bignum MATCHES "gmp")
  target_include_directories(secp256k1 PUBLIC ${GMP_INSTALL_PREFIX}/include)
endif()

target_link_libraries(secp256k1 PUBLIC OpenSSL::Crypto)
if (GMP_LIB)
  target_link_libraries(secp256k1 PUBLIC ${GMP_LIB})
endif()

if (enable_module_ecdh)
  add_subdirectory(modules/ecdh)
endif()
if (enable_module_recovery)
  add_subdirectory(modules/recovery)
endif()
if (enable_module_extrakeys)
  add_subdirectory(modules/extrakeys)
endif()
if (enable_module_schnorrsig)
  add_subdirectory(modules/schnorrsig)
endif()

if (use_benchmark)
  add_executable(bench_verify bench_verify.c)
  target_link_libraries(bench_verify secp256k1)

  add_executable(bench_sign bench_sign.c)
  target_link_libraries(bench_sign secp256k1)

  add_executable(bench_internal bench_internal.c)
  target_link_libraries(bench_internal secp256k1)

  add_executable(bench_ecmult bench_ecmult.c)
  target_link_libraries(bench_ecmult secp256k1)
endif()

if (use_tests)
  add_executable(tests tests.c)
  if (enable_valgrind)
    add_compile_definitions(VALGRIND=1)
    add_executable(valgrind_ctime_test valgrind_ctime_test.c)
    target_link_libraries(valgrind_ctime_test secp256k1)
  endif()
  if (NOT enable_coverage)
    target_compile_definitions(tests PRIVATE VERIFY=1)
  endif()
  target_link_libraries(tests secp256k1)

  if (use_exhaustive_tests)
    add_executable(exhaustive_tests tests_exhaustive.c)
    target_link_libraries(exhaustive_tests secp256k1)
    if (NOT enable_coverage)
      target_compile_definitions(exhaustive_tests PRIVATE VERIFY=1)
    endif()

    add_test(NAME exhaustive_tests COMMAND exhaustive_tests)
  endif()

  add_test(NAME tests COMMAND tests)
endif()
