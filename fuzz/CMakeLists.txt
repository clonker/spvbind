# Differential fuzzing of SPIRV-Reflect against spvbind, see README.md.
#
# Always: reflect_dump, SPIRV-Reflect's push constant blocks in the format of `spvbind --locations`, for
# differential.py. With SPVBIND_FUZZTEST: spvbind_fuzz, FuzzTest targets that run SPIRV-Reflect and spvbind's compiled
# Lean code in one process; configure with Clang and FUZZTEST_FUZZING_MODE=ON for coverage-guided fuzzing.
cmake_minimum_required(VERSION 3.24)
project(spvbind_fuzz C CXX)

set(SPIRV_REFLECT_SOURCE_DIR "" CACHE PATH "A checkout of SPIRV-Reflect; fetched from GitHub if empty")
set(SPIRV_REFLECT_GIT_TAG "main" CACHE STRING "The SPIRV-Reflect revision to fetch if SPIRV_REFLECT_SOURCE_DIR is empty")
option(SPVBIND_FUZZ_SANITIZE "Build reflect_dump with AddressSanitizer and UndefinedBehaviorSanitizer" OFF)
option(SPVBIND_FUZZTEST "Build spvbind_fuzz, the FuzzTest targets (fetches FuzzTest and its dependencies)" OFF)
set(FUZZTEST_SOURCE_DIR "" CACHE PATH "A checkout of FuzzTest; fetched from GitHub if empty")
set(FUZZTEST_GIT_TAG "2026-06-29" CACHE STRING "The FuzzTest revision to fetch if FUZZTEST_SOURCE_DIR is empty")
option(SPVBIND_FUZZ_PATCH_SPIRV_REFLECT
    "Apply patches/spirv-reflect-known-bugs.patch to the fetched SPIRV-Reflect, so that fuzzing gets past the known crashes and wrong results" OFF)
find_program(SPVBIND_GLSLC glslc DOC "To compile the seed shaders in tests/accepted")

include(FetchContent)
set(spirvReflectPatch "${CMAKE_CURRENT_SOURCE_DIR}/patches/spirv-reflect-known-bugs.patch")
if(SPIRV_REFLECT_SOURCE_DIR)
    set(spirv_reflect_SOURCE_DIR "${SPIRV_REFLECT_SOURCE_DIR}")
    if(SPVBIND_FUZZ_PATCH_SPIRV_REFLECT)
        message(STATUS "SPVBIND_FUZZ_PATCH_SPIRV_REFLECT does not touch SPIRV_REFLECT_SOURCE_DIR; apply ${spirvReflectPatch} yourself")
    endif()
else()
    set(patchCommand)
    if(SPVBIND_FUZZ_PATCH_SPIRV_REFLECT)
        set(patchCommand PATCH_COMMAND git apply "${spirvReflectPatch}")
    endif()
    FetchContent_Declare(spirv_reflect
        GIT_REPOSITORY https://github.com/KhronosGroup/SPIRV-Reflect
        GIT_TAG "${SPIRV_REFLECT_GIT_TAG}"
        GIT_SHALLOW TRUE
        SOURCE_SUBDIR does-not-exist  # only the sources are wanted, not SPIRV-Reflect's own CMake project
        ${patchCommand}
    )
    FetchContent_MakeAvailable(spirv_reflect)
endif()

if(SPVBIND_FUZZTEST)
    # FuzzTest's flags (coverage, AddressSanitizer in fuzzing mode) apply to every target below, SPIRV-Reflect and the
    # Lean code included, so that both guide the fuzzer.
    if(FUZZTEST_SOURCE_DIR)
        add_subdirectory("${FUZZTEST_SOURCE_DIR}" fuzztest)
    else()
        FetchContent_Declare(fuzztest
            GIT_REPOSITORY https://github.com/google/fuzztest
            GIT_TAG "${FUZZTEST_GIT_TAG}"
        )
        FetchContent_MakeAvailable(fuzztest)
    endif()
    fuzztest_setup_fuzzing_flags()
endif()

# SPIRV-Reflect, and its view of push constant blocks.
add_library(spvbind_fuzz_reflect STATIC reflect_locations.cpp reflect_locations.hpp "${spirv_reflect_SOURCE_DIR}/spirv_reflect.c")
target_include_directories(spvbind_fuzz_reflect PUBLIC "${spirv_reflect_SOURCE_DIR}" "${CMAKE_CURRENT_SOURCE_DIR}")
target_compile_features(spvbind_fuzz_reflect PUBLIC cxx_std_17)
set_source_files_properties("${spirv_reflect_SOURCE_DIR}/spirv_reflect.c" PROPERTIES COMPILE_OPTIONS "-w")

add_executable(reflect_dump reflect_dump.cpp)
target_link_libraries(reflect_dump PRIVATE spvbind_fuzz_reflect)
if(SPVBIND_FUZZ_SANITIZE AND NOT SPVBIND_FUZZTEST)
    foreach(target spvbind_fuzz_reflect reflect_dump)
        target_compile_options(${target} PRIVATE -fsanitize=address,undefined -fno-omit-frame-pointer -g)
        target_link_options(${target} PRIVATE -fsanitize=address,undefined)
    endforeach()
endif()

if(NOT SPVBIND_FUZZTEST)
    return()
endif()

# spvbind: the C that Lake compiled the Spec and Spvbind libraries to, with Lean's runtime. `lake build` first.
execute_process(COMMAND lean --print-prefix OUTPUT_VARIABLE LEAN_PREFIX OUTPUT_STRIP_TRAILING_WHITESPACE
    RESULT_VARIABLE leanResult)
if(NOT leanResult EQUAL 0)
    message(FATAL_ERROR "lean not found; install elan and run lake build in ${CMAKE_CURRENT_SOURCE_DIR}/..")
endif()
set(leanIr "${CMAKE_CURRENT_SOURCE_DIR}/../.lake/build/ir")
file(GLOB leanSources "${leanIr}/Spec.c" "${leanIr}/Spec/*.c" "${leanIr}/Spvbind.c" "${leanIr}/Spvbind/*.c")
if(NOT EXISTS "${leanIr}/Spvbind/Oracle.c")
    message(FATAL_ERROR "${leanIr}/Spvbind/Oracle.c not found; run lake build in ${CMAKE_CURRENT_SOURCE_DIR}/..")
endif()
add_library(spvbind_fuzz_oracle STATIC oracle.cpp oracle.hpp ${leanSources})
target_include_directories(spvbind_fuzz_oracle PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}" PRIVATE "${LEAN_PREFIX}/include")
target_compile_features(spvbind_fuzz_oracle PUBLIC cxx_std_17)
set_source_files_properties(${leanSources} PROPERTIES COMPILE_OPTIONS "-w;-ffp-contract=off;-fstack-clash-protection")
target_link_libraries(spvbind_fuzz_oracle PUBLIC "${LEAN_PREFIX}/lib/lean/libleanshared.so")
set_target_properties(spvbind_fuzz_oracle PROPERTIES BUILD_RPATH "${LEAN_PREFIX}/lib/lean")

# Seeds: the example and the accepted test cases, compiled if glslc is available.
set(seedDir "${CMAKE_CURRENT_BINARY_DIR}/seeds")
file(MAKE_DIRECTORY "${seedDir}")
file(COPY "${CMAKE_CURRENT_SOURCE_DIR}/../examples/params.spv" DESTINATION "${seedDir}")
if(SPVBIND_GLSLC)
    file(GLOB seedShaders "${CMAKE_CURRENT_SOURCE_DIR}/../tests/accepted/*.comp")
    foreach(shader IN LISTS seedShaders)
        get_filename_component(name "${shader}" NAME_WE)
        execute_process(COMMAND "${SPVBIND_GLSLC}" --target-env=vulkan1.3 -o "${seedDir}/${name}.spv" "${shader}"
            RESULT_VARIABLE glslcResult)
        if(NOT glslcResult EQUAL 0)
            message(WARNING "glslc failed on ${shader}")
        endif()
    endforeach()
endif()

add_executable(spvbind_fuzz differential_fuzz.cpp)
target_link_libraries(spvbind_fuzz PRIVATE spvbind_fuzz_reflect spvbind_fuzz_oracle)
target_compile_definitions(spvbind_fuzz PRIVATE
    SPVBIND_FUZZ_SEEDS="${seedDir}"
    SPVBIND_FUZZ_FINDINGS_DEFAULT="${CMAKE_CURRENT_SOURCE_DIR}/findings"
)
link_fuzztest(spvbind_fuzz)
set_target_properties(spvbind_fuzz PROPERTIES BUILD_RPATH "${LEAN_PREFIX}/lib/lean")
enable_testing()
include(GoogleTest)
gtest_discover_tests(spvbind_fuzz)
