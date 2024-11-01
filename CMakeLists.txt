cmake_minimum_required(VERSION 3.14)

set(OPENSMT_VERSION_MAJOR 2)
set(OPENSMT_VERSION_MINOR 8)
set(OPENSMT_VERSION_PATCH 1)
set(OPENSMT_VERSION ${OPENSMT_VERSION_MAJOR}.${OPENSMT_VERSION_MINOR}.${OPENSMT_VERSION_PATCH})
project(opensmt VERSION ${OPENSMT_VERSION} LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 20)

set(CMAKE_SOURCE_DIR "${PROJECT_SOURCE_DIR}/src")

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
option(EXPLICIT_CONGRUENCE_EXPLANATIONS "Construct explicit congruence explanations" OFF)
option(MATRIX_DEBUG "Trace matrix operations (noisy output)" OFF)
option(STATISTICS "Compute and print solver's statistics" OFF)

option(ENABLE_LINE_EDITING "Enable line editing with libedit" OFF)

option(BUILD_STATIC_LIBS "Build static library" ON)
option(BUILD_SHARED_LIBS "Build shared library" ON)
option(BUILD_EXECUTABLES "Build executables" ON)
option(PARALLEL "Build parallel library" OFF)

option(PACKAGE_TESTS "Build the tests" ON)
option(PACKAGE_BENCHMARKS "Build the benchmarks" OFF)

option(MAXIMALLY_STATIC_BINARY "Link to static versions of the libraries as much as reasonably possible" OFF)

if (MAXIMALLY_STATIC_BINARY)
    MESSAGE("Building maximally static binaries.  Shared libraries and unit tests will not be built")
    set(FORCE_STATIC_GMP ON)
    set(BUILD_SHARED_LIBS OFF)
    set(PACKAGE_TESTS OFF)
    set(PACKAGE_BENCHMARKS OFF)
endif(MAXIMALLY_STATIC_BINARY)

find_package(GMP REQUIRED)

set(THREADS_PREFER_PTHREAD_FLAG ON)
find_package(Threads REQUIRED)


include_directories(
    ${CMAKE_SOURCE_DIR}
    ${GMP_INCLUDE_DIR}
)


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
endif()

if (EXPLICIT_CONGRUENCE_EXPLANATIONS)
  add_definitions(-DEXPLICIT_CONGRUENCE_EXPLANATIONS)
endif()

if (MATRIX_DEBUG)
    add_definitions(-DENABLE_MATRIX_TRACE)
endif()

add_subdirectory(${CMAKE_SOURCE_DIR})

################# TESTING #############################################
if(PACKAGE_TESTS)
    if (NOT BUILD_SHARED_LIBS)
      message(FATAL_ERROR "Building tests requires shared libraries")
    endif()
    enable_testing()
    add_subdirectory(${PROJECT_SOURCE_DIR}/test)
endif()
#########################################################################
################# BENCHMARKING ##########################################

if (PACKAGE_BENCHMARKS)
    add_subdirectory(${PROJECT_SOURCE_DIR}/benchmark)
endif()

#########################################################################
install(FILES ${CMAKE_SOURCE_DIR}/opensmt2.h DESTINATION ${INSTALL_HEADERS_DIR})
