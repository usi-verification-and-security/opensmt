cmake_minimum_required(VERSION 3.3)

if (POLICY CMP0074) # Policy 0074 has been introduced in CMake 3.12, so we need a check, otherwise older version would give an error
cmake_policy(SET CMP0074 NEW)
endif()

set(OPENSMT_VERSION_MAJOR 2)
set(OPENSMT_VERSION_MINOR 2)
set(OPENSMT_VERSION_PATCH 1)
set(OPENSMT_VERSION ${OPENSMT_VERSION_MAJOR}.${OPENSMT_VERSION_MINOR}.${OPENSMT_VERSION_PATCH})
project(opensmt VERSION ${OPENSMT_VERSION} LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)

set(CMAKE_SOURCE_DIR "src")

get_filename_component(CMAKE_MODULE_PATH
"${CMAKE_SOURCE_DIR}/../cmake_modules/" ABSOLUTE)

set(CMAKE_POSITION_INDEPENDENT_CODE ON)

#message(${CMAKE_C_COMPILER_ID})
#message(${CMAKE_CXX_COMPILER_ID})

#Set the default build type if this is the first time cmake is run and nothing has been set
if (NOT EXISTS ${CMAKE_BINARY_DIR}/CMakeCache.txt)
  if (NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE "Release" CACHE STRING "Choose the type of build, options are: None Debug Release RelWithDebInfo MinSizeRel." FORCE)
  endif()
endif()

set(INSTALL_HEADERS_DIR include/opensmt)

option(PARTITION_PRETTYPRINT "Term pretty printing shows partitions" OFF)
option(ITP_DEBUG "Debug interpolation" OFF)
option(PEDANTIC_DEBUG "Pedantic debug" OFF)
option(DEBUG_SIMPLIFICATION "Debug simplification" OFF)
option(VERBOSE_FOPS "Verbose file operations" OFF)
option(VERBOSE_SAT "Verbose sat" OFF)
option(PRINT_UNITS "Print units" OFF)
option(DEBUG_GC "Debug garbage collection" OFF)
option(LADEBUG "Debug lookahead" OFF)
option(PRINT_DECOMPOSED_STATS "Print statistics about decomposed interpolants" OFF)
option(STATISTICS "Compute and print solver's statistics" OFF)
option(ENABLE_LINE_EDITING "Enable line editing with readline or libedit" OFF)
option(USE_READLINE "Use readline over libedit" OFF)
option(BUILD_STATIC_LIBS "Build static library" ON)
option(BUILD_SHARED_LIBS "Build shared library" ON)
option(BUILD_EXECUTABLES "Build executables" ON)
option(EXPLICIT_CONGRUENCE_EXPLANATIONS "Construct explicit congruence explanations" OFF)
option(MATRIX_DEBUG "Trace matrix operations (noisy output)" OFF)

find_package(GMP REQUIRED)

set(THREADS_PREFER_PTHREAD_FLAG ON)
find_package(Threads REQUIRED)


include_directories(
    ${CMAKE_SOURCE_DIR}/minisat/mtl
    ${CMAKE_SOURCE_DIR}/minisat/core
    ${CMAKE_SOURCE_DIR}/common
    ${CMAKE_SOURCE_DIR}/sorts
    ${CMAKE_SOURCE_DIR}/symbols
    ${CMAKE_SOURCE_DIR}/options
    ${CMAKE_SOURCE_DIR}/api
    ${CMAKE_SOURCE_DIR}/tsolvers
    ${CMAKE_SOURCE_DIR}/tsolvers/egraph
    ${CMAKE_SOURCE_DIR}/tsolvers/lasolver
    ${CMAKE_SOURCE_DIR}/tsolvers/stpsolver
    ${CMAKE_SOURCE_DIR}/tsolvers/lrasolver
    ${CMAKE_SOURCE_DIR}/tsolvers/liasolver
    ${CMAKE_SOURCE_DIR}/cnfizers
    ${CMAKE_SOURCE_DIR}/pterms
    ${CMAKE_SOURCE_DIR}/logics
    ${CMAKE_SOURCE_DIR}/smtsolvers
    ${CMAKE_SOURCE_DIR}/parsers/smt2new
    ${CMAKE_SOURCE_DIR}/simplifiers
    ${CMAKE_SOURCE_DIR}/rewriters
    ${CMAKE_SOURCE_DIR}/proof
    ${CMAKE_SOURCE_DIR}/models
    ${CMAKE_SOURCE_DIR}/itehandler
)

#######################################################################################################
# workaround for older versions of CMake where we cannot use target_link_libraries for object libraries
get_property(GMP_INCLUDE_DIRS TARGET GMP::GMP PROPERTY INTERFACE_INCLUDE_DIRECTORIES)
if (NOT GMP_INCLUDE_DIRS)
    message(FATAL_ERROR "GMP includes not found")
endif()
include_directories(${GMP_INCLUDE_DIRS})
#######################################################################################################


if (BUILD_EXECUTABLES AND NOT BUILD_STATIC_LIBS)
  message(FATAL_ERROR "Cannot build executables without also building static libraries")
endif()

if (ITP_DEBUG)
    add_definitions(-DITP_DEBUG)
endif (ITP_DEBUG)

if (PEDANTIC_DEBUG)
    add_definitions(-DPEDANTIC_DEBUG)
endif(PEDANTIC_DEBUG)

if(DEBUG_SIMPLIFICATION)
    add_definitions(-DSIMPLIFY_DEBUG)
endif()

if(DEBUG_GC)
    add_definitions(-DGC_DEBUG)
endif()

if(VERBOSE_FOPS)
    add_definitions(-DVERBOSE_FOPS)
endif(VERBOSE_FOPS)

if (LADEBUG)
    add_definitions(-DLADEBUG)
endif ()

if(STATISTICS)
    add_definitions(-DSTATISTICS)
endif(STATISTICS)

if (ENABLE_LINE_EDITING)
  add_definitions(-DENABLE_LINE_EDITING)
  if (USE_READLINE)
    add_definitions(-DUSE_READLINE)
  endif()
endif()

if (EXPLICIT_CONGRUENCE_EXPLANATIONS)
  add_definitions(-DEXPLICIT_CONGRUENCE_EXPLANATIONS)
endif()

if (MATRIX_DEBUG)
    add_definitions(-DENABLE_MATRIX_TRACE)
endif()

add_subdirectory(${CMAKE_SOURCE_DIR})

################# TESTING #############################################
option(PACKAGE_TESTS "Build the tests" ON)
if(PACKAGE_TESTS)
    if (NOT BUILD_STATIC_LIBS)
      message(FATAL_ERROR "Building tests requires static libraries")
    endif()
    if(CMAKE_VERSION VERSION_LESS 3.11)
        MESSAGE(WARNING "Minimum CMAKE version for building tests is 3.11")
    else(CMAKE_VERSION VERSION_LESS 3.11)
        enable_testing()
        add_subdirectory(${PROJECT_SOURCE_DIR}/test)
    endif(CMAKE_VERSION VERSION_LESS 3.11)
endif()
#########################################################################
################# BENCHMARKING ##########################################
option(PACKAGE_BENCHMARKS "Build the benchmarks" OFF)
if (PACKAGE_BENCHMARKS)
    if(CMAKE_VERSION VERSION_LESS 3.11)
        MESSAGE(WARNING "Minimum CMAKE version for building benchmarking is 3.11")
    else()
        add_subdirectory(${PROJECT_SOURCE_DIR}/benchmark)
    endif()
endif()

#########################################################################
install(FILES ${CMAKE_SOURCE_DIR}/opensmt2.h DESTINATION ${INSTALL_HEADERS_DIR})

if (ENABLE_LINE_EDITING AND USE_READLINE)
  message("You have chosen to build OpenSMT against optional GPL-licensed components (readline)."
          "\n"
          "As these libraries are covered under the GPL, so will the resulting binary of OpenSMT.")
endif()

