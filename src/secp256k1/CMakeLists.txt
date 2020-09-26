cmake_minimum_required(VERSION 3.18)
include(CheckCCompilerFlag)
include(CheckIncludeFiles)
include(CheckLanguage)

project(libsecp256k1
  VERSION 0.1
  DESCRIPTION "Optimized C library for EC operations on curve secp256k1"
  HOMEPAGE_URL "https://github.com/bitcoin-core/secp256k1"
  LANGUAGES C)

enable_testing()

option(use_benchmark "compile benchmark" ON)
option(enable_coverage "enable compiler flags to support kcov coverage analysis" OFF)
option(use_tests "compile tests" ON)
set(enable_openssl_tests "auto" CACHE STRING "enable OpenSSL tests")
option(use_experimental "allow experimental configure options" OFF)
option(use_exhaustive_tests "compile exhaustive tests" ON)
option(use_endomorphism "enable endomorphism" OFF)
set(use_ecmult_static_precomputation "auto" CACHE STRING "enable precomputed ecmult table for \
  signing")
option(enable_module_ecdh "enable ECDH shared secret computation" ${use_experimental})
option(enable_module_recovery "enable ECDSA pubkey recovery module" OFF)
option(enable_module_extrakeys "enable extrakeys module" ${use_experimental})
option(enable_module_schnorrsig "enable schnorrsig module" ${use_experimental})
option(use_external_default_callbacks "enable external default callback functions"
  OFF)
set(set_widemul "auto" CACHE STRING "override test widemul setting \
(int64|int128|auto)")
set(req_bignum "auto" CACHE STRING "bignum implementation to use (gmp|no|auto)")
set(req_asm "auto" CACHE STRING "assembly optimizations to use (experimental: arm) \
(x86_64|arm|no|auto)")
set(req_ecmult_window "auto" CACHE STRING "window size for ecmult \
precomputation for verification, specified as integer in range [2..24]. Larger \
values result in possibly better performance at the cost of an exponentially \
larger precomputed table. The table will store 2^(SIZE-2) * 64 bytes of data \
but can be larger in memory due to platform-specific padding and alignment. If \
the endomorphism optimization is enabled, two tables of this size are used \
instead of only one.  auto is a reasonable setting for desktop machines \
(currently 15).")
set(req_ecmult_gen_precision "auto" CACHE STRING "Precision bits to tune the \
precomputed table size for signing. The size of the table is 32kB for 2 bits, \
64kB for 4 bits, 512kB for 8 bits of precision. A larger table size usually \
results in possible faster signing. auto is a reasonable setting for desktop \
machines (currently 4).")

foreach(FLAG -std=c89 -pedantic -Wall -Wextra -Wcast-align -Wnested-externs
    -Wshadow -Wstrict-prototypes -Wno-unused-function -Wno-long-long
    -Wno-overlength-strings -fvisibility=hidden)
  check_c_compiler_flag(${FLAG} CC_SUPPORTS_${FLAG})
  if (CC_SUPPORTS_${FLAG})
    set(CMAKE_C_FLAGS "${FLAG} ${CMAKE_C_FLAGS}")
  endif()
endforeach()

add_compile_definitions(SECP256K1_BUILD=1)

check_include_files("valgrind/memcheck.h" enable_valgrind)
if (enable_valgrind)
  set(enable_valgrind ON)
  add_compile_definitions(VALGRIND_ENABLED=1)
else()
  set(enable_valgrind OFF)
endif()

if (enable_coverage)
  add_compile_definitions(COVERAGE=1)
  set(CMAKE_C_FLAGS "-O0 --coverage ${CMAKE_C_FLAGS}")
  set(CMAKE_EXE_LINKER_FLAGS_INIT "--coverage ${CMAKE_EXE_LINKER_FLAGS_INIT}")
  set(CMAKE_SHARED_LINKER_FLAGS_INIT "--coverage ${CMAKE_SHARED_LINKER_FLAGS_INIT}")
  set(CMAKE_MODULE_LINKER_FLAGS_INIT "--coverage ${CMAKE_MODULE_LINKER_FLAGS_INIT}")
else()
  set(CMAKE_C_FLAGS "-O2 ${CMAKE_C_FLAGS}")
endif()

if (use_ecmult_static_precomputation MATCHES "auto|ON")
  check_c_compiler_flag(-Wall SUPPORTS_Wall)
  check_c_compiler_flag(-Wextra SUPPORTS_Wextra)
  check_c_compiler_flag(-Wno-unused-function SUPPORTS_Wno_unused_function)
  if (SUPPORTS_Wall AND SUPPORTS_Wextra AND
      SUPPORTS_Wno_unused_function)
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wall -Wextra -Wno-unused-function")
  endif()
  set(set_precomp ON)
else()
  set(set_precomp OFF)
endif()

if (req_asm MATCHES "auto")
  check_language(ASM)
  if (CMAKE_ASM_COMPILER)
    enable_language(ASM)
    set(set_asm "x86_64" CACHE STRING "asm type")
  else()
    set(set_asm "no")
  endif()
else()
  set(set_asm ${req_asm})
  if (set_asm MATCHES "x86_64")
    check_language(ASM)
    if (CMAKE_ASM_COMPILER)
      enable_language(ASM)
    else()
      message(FATAL_ERROR "x86_64 assembly optimization requested but not \
      available")
    endif()
  elseif (NOT set_asm MATCHES "arm|no")
    message(FATAL_ERROR "invalid assembly optimization selection")
  endif()
endif()

# On macOS, Homebrew installed packages like OpenSSL may not be linked into
# their normal locations.
if (CMAKE_HOST_SYSTEM_NAME MATCHES "Darwin")
  find_program(HOMEBREW_EXE brew)
  if (HOMEBREW_EXE)
    execute_process(COMMAND ${HOMEBREW_EXE} --prefix openssl OUTPUT_VARIABLE
      OPENSSL_INSTALL_PREFIX OUTPUT_STRIP_TRAILING_WHITESPACE)
    execute_process(COMMAND ${HOMEBREW_EXE} --prefix gmp OUTPUT_VARIABLE
      GMP_INSTALL_PREFIX OUTPUT_STRIP_TRAILING_WHITESPACE)
    list(APPEND CMAKE_PREFIX_PATH "${OPENSSL_INSTALL_PREFIX}")
    list(APPEND CMAKE_PREFIX_PATH "${GMP_INSTALL_PREFIX}")
  endif()
endif()

if (req_bignum MATCHES "auto")
  find_library(GMP_LIB gmp)
  if (GMP_LIB)
    set(set_bignum "gmp" CACHE STRING "bignum library")
  else()
    set(set_bignum "no")
  endif()
else()
  set(set_bignum ${req_bignum})
  if (set_bignum MATCHES "gmp")
    find_library(GMP_LIB gmp)
    if (NOT set_bignum)
      message(FATAL_ERROR "gmp bignum explicitly requested but libgmp not
      available")
    endif()
  elseif (NOT set_bignum MATCHES "no")
    message(STATUS "${set_bignum}")
    message(FATAL_ERROR "invalid bignum implementation selection")
  endif()
endif()

# Select assembly optimization
if (set_asm MATCHES "x86_64")
  add_compile_definitions(USE_ASM_X86_64=1)
elseif (set_asm MATCHES "arm")
  message(STATUS "setasm is arm")
  set(use_external_asm ON)
elseif (NOT set_asm MATCHES "no")
  message(FATAL_ERROR "invalid assembly optimizations")
endif()

# Select wide multiplication implementation
if (set_widemul MATCHES "int128")
  add_compile_definitions(USE_FORCE_WIDEMUL_INT128=1)
elseif (set_widemul MATCHES "int64")
  add_compile_definitions(USE_FORCE_WIDEMUL_INT64=1)
elseif (NOT set_widemul MATCHES "auto")
  message(FATAL_ERROR "invalid wide multiplication implementation")
endif()

# Select bignum implementation
if (set_bignum MATCHES "gmp")
  add_compile_definitions(HAVE_LIBGMP=1 USE_NUM_GMP=1 USE_FIELD_INV_NUM=1
    USE_SCALAR_INV_NUM=1)
elseif (set_bignum MATCHES "no")
  add_compile_definitions(USE_NUM_NONE=1 USE_FIELD_INV_BUILTIN=1
    USE_SCALAR_INV_BUILTIN=1)
else()
  message(FATAL_ERROR "invalid bignum implementation")
endif()

# Set ecmult window size
if (req_ecmult_window MATCHES "auto")
  set(set_ecmult_window "15")
else()
  set(set_ecmult_window ${req_ecmult_window})
endif()

set(error_window_size "window size for ecmult precomputation not an integer in \
range [2..24] or 'auto'")
if (set_ecmult_window MATCHES "''|.*[^0-9].*")
  message(FATAL_ERROR "${error_window_size}")
elseif (set_ecmult_window LESS "2" OR set_ecmult_window GREATER "24")
  message(FATAL_ERROR "${error_window_size}")
else()
  add_compile_definitions(ECMULT_WINDOW_SIZE=${set_ecmult_window})
endif()

if (req_ecmult_gen_precision MATCHES "auto")
  set(set_ecmult_gen_precision "4")
else()
  set(set_ecmult_gen_precision ${req_ecmult_gen_precision})
endif()

if (set_ecmult_gen_precision MATCHES "2|4|8")
  add_compile_definitions(ECMULT_GEN_PREC_BITS=${set_ecmult_gen_precision})
else()
  message(FATAL_ERROR "ecmult gen precision not 2, 4, 8 or 'auto'")
endif()


if (use_tests)
  find_package(OpenSSL REQUIRED)
  list(APPEND CMAKE_REQUIRED_LIBRARIES "OpenSSL::Crypto")
  check_include_files("openssl/ec.h;openssl/ecdsa.h;openssl/obj_mac.h"
    has_openssl_ec)
  if (has_openssl_ec)
    if (NOT enable_openssl_tests MATCHES "OFF")
      add_compile_definitions(ENABLE_OPENSSL_TESTS=1)
    endif()
  elseif(enable_openssl_tests MATCHES "ON")
    message(FATAL_ERROR "OpenSSL tests requested but OpenSSL with EC support is
    not available")
  endif()
elseif(enable_openssl_tests MATCHES "ON")
  message(FATAL_ERROR "OpenSSL tests requested but tests are not enabled")
endif()

if (use_endomorphism)
  add_compile_definitions(USE_ENDOMORPHISM=1)
endif()

if (set_precomp)
  add_compile_definitions(USE_ECMULT_STATIC_PRECOMPUTATION=1)
endif()

if (enable_module_ecdh)
  add_compile_definitions(ENABLE_MODULE_ECDH=1)
endif()

if (enable_module_recovery)
  add_compile_definitions(ENABLE_MODULE_RECOVERY=1)
endif()

if (enable_module_schnorrsig)
  add_compile_definitions(ENABLE_MODULE_SCHNORRSIG=1)
  set(enable_module_extrakeys ON)
endif()

# Test if extrakeys is set after the schnorrsig module to allow the schnorrsig
# module to set enable_module_extrakeys=yes
if (enable_module_extrakeys)
  add_compile_definitions(ENABLE_MODULE_EXTRAKEYS=1)
endif()

if (use_external_asm)
  add_compile_definitions(USE_EXTERNAL_ASM=1)
endif()

if (use_external_default_callbacks)
  add_compile_definitions(USE_EXTERNAL_DEFAULT_CALLBACKS=1)
endif()

if (use_experimental)
  message(STATUS "******")
  message(STATUS "WARNING: experimental build")
  message(STATUS "Experimental features do not have stable APIs or properties, and may not be safe for production use.")
  message(STATUS "Building ECDH module: ${enable_module_ecdh}")
  message(STATUS "Building extrakeys module: ${enable_module_extrakeys}")
  message(STATUS "Building schnorrsig module: ${enable_module_schnorrsig}")
  message(STATUS "******")
else()
  if (enable_module_ecdh)
    message(FATAL_ERROR "ECDH module is experimental. Use -Duse_experimental \
    to allow.")
  endif()
  if (enable_module_extrakeys)
    message(FATAL_ERROR "extrakeys module is experimental. Use \
    -Duse_experimental to allow")
  endif()
  if (enable_module_schnorrsig)
    message(FATAL_ERROR "schnorrsig module is experimental. Use \
    -Duse_experimental to allow.")
  endif()
  if (set_asm MATCHES "arm")
    message(FATAL_ERROR "ARM assembly optimization is experimental. Use \
    -Duse_experimental to allow")
  endif()
endif()


#add_subdirectory(include)
add_subdirectory(src)

message(STATUS "Build Options:")
message(STATUS "  with endomorphism       = ${use_endomorphism}")
message(STATUS "  with ecmult precomp     = ${set_precomp}")
message(STATUS "  with external callbacks = ${use_external_default_callbacks}")
message(STATUS "  with benchmarks         = ${use_benchmark}")
message(STATUS "  with coverage           = ${enable_coverage}")
message(STATUS "  module ecdh             = ${enable_module_ecdh}")
message(STATUS "  module recovery         = ${enable_module_recovery}")
message(STATUS "  module extrakeys        = ${enable_module_extrakeys}")
message(STATUS "  module schnorrsig       = ${enable_module_schnorrsig}")
message(STATUS)
message(STATUS "  asm                     = ${set_asm}")
message(STATUS "  bignum                  = ${set_bignum}")
message(STATUS "  ecmult window size      = ${set_ecmult_window}")
message(STATUS "  ecmult gen prec. bits   = ${set_ecmult_gen_precision}")

# Hide test-only options unless they're used.
if (NOT set_widemul MATCHES "auto")
  message(STATUS "  wide multiplication     = ${set_widemul}")
endif()
message(STATUS)
message(STATUS "  valgrind                = ${enable_valgrind}")
message(STATUS "  CC                      = ${CMAKE_C_COMPILER}")
message(STATUS "  CFLAGS                  = ${CMAKE_C_FLAGS}")
message(STATUS "  CPPFLAGS                = ${CMAKE_CXX_FLAGS}")
message(STATUS "  LDFLAGS                 = ${CMAKE_EXE_LINKER_FLAGS_INIT}")
