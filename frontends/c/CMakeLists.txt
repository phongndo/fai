# fai-cc: a C compiler on FIR, from Clang's AST through FIR's C API. See README.md.
cmake_minimum_required(VERSION 3.20)
project(fai-cc LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release)
endif()

find_package(Clang REQUIRED CONFIG)
message(STATUS "Clang ${LLVM_PACKAGE_VERSION} from ${Clang_DIR}")

get_filename_component(REPO "${CMAKE_CURRENT_SOURCE_DIR}/../.." ABSOLUTE)

# FIR's C API: the header, and the static library cargo builds. By default this build runs
# `cargo build --release -p fir-capi` (a no-op when nothing changed); a caller that builds the
# library itself passes FIR_CAPI_LIB and FAI_CC_BUILD_CAPI=OFF.
option(FAI_CC_BUILD_CAPI "Build libfir_capi.a with cargo" ON)
set(FIR_CAPI_LIB "${REPO}/target/release/libfir_capi.a" CACHE FILEPATH "libfir_capi.a")
if(FAI_CC_BUILD_CAPI)
  find_program(CARGO cargo REQUIRED)
  add_custom_target(fir-capi
    COMMAND "${CARGO}" build --release -p fir-capi
    WORKING_DIRECTORY "${REPO}"
    BYPRODUCTS "${FIR_CAPI_LIB}"
    COMMENT "Building libfir_capi.a"
    USES_TERMINAL)
endif()

# Clang's resource directory (its own headers: stddef.h, stdint.h, …), from the compiler of the
# same release that builds this tool; FAI_CC_RESOURCE_DIR overrides it at run time.
execute_process(
  COMMAND "${CMAKE_CXX_COMPILER}" -print-resource-dir
  OUTPUT_VARIABLE FAI_CC_RESOURCE_DIR
  OUTPUT_STRIP_TRAILING_WHITESPACE)

add_executable(fai-cc src/main.cpp src/Lower.cpp)
target_include_directories(fai-cc PRIVATE "${REPO}/crates/fir-capi/include")
target_include_directories(fai-cc SYSTEM PRIVATE ${CLANG_INCLUDE_DIRS} ${LLVM_INCLUDE_DIRS})
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND "${LLVM_DEFINITIONS}")
target_compile_options(fai-cc PRIVATE ${LLVM_DEFINITIONS_LIST})
target_compile_definitions(fai-cc PRIVATE FAI_CC_RESOURCE_DIR="${FAI_CC_RESOURCE_DIR}")
target_compile_options(fai-cc PRIVATE -Wall -Wextra -Werror)
if(NOT LLVM_ENABLE_RTTI)
  target_compile_options(fai-cc PRIVATE -fno-rtti)
endif()
if(FAI_CC_BUILD_CAPI)
  add_dependencies(fai-cc fir-capi)
endif()

# One shared library for Clang and one for LLVM when the installation has them (nixpkgs does),
# else the component libraries.
if(TARGET clang-cpp AND TARGET LLVM)
  set(CLANG_LIBS clang-cpp LLVM)
else()
  set(CLANG_LIBS clangTooling clangFrontend clangSerialization clangDriver clangParse clangSema
    clangAnalysis clangAST clangASTMatchers clangEdit clangLex clangBasic)
endif()
target_link_libraries(fai-cc PRIVATE ${CLANG_LIBS} "${FIR_CAPI_LIB}")
if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
  target_link_libraries(fai-cc PRIVATE pthread dl m)
endif()
