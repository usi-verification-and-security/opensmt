cmake_minimum_required(VERSION 3.3)
project(opensmt VERSION 2.0.0 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 11)

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
option(DEBUG_REASONS "Debug ..." OFF)
option(DEBUG_SIMPLIFICATION "Debug simplification" OFF)
option(VERBOSE_EUF "Verbose EUF" OFF)
option(VERBOSE_EUFEX "Verbose EUF with explanation" OFF)
option(VERBOSE_FOPS "Verbose file operations" OFF)
option(VERBOSE_SAT "Verbose sat" OFF)
option(PRINT_UNITS "Print units" OFF)
option(DEBUG_GC "Debug garbage collection" OFF)
option(LADEBUG "Debug lookahead" OFF)
option(PRINT_DECOMPOSED_STATS "Print statistics about decomposed interpolants" OFF)
option(STATISTICS "Compute and print solver's statistics" OFF)
option(USE_READLINE "Use readline over libedit" OFF)

if (NOT USE_READLINE)
  find_package(LibEdit REQUIRED)
else()
  find_package(Readline REQUIRED)
endif()

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
    ${CMAKE_SOURCE_DIR}/cnfizers
    ${CMAKE_SOURCE_DIR}/pterms
    ${CMAKE_SOURCE_DIR}/logics
    ${CMAKE_SOURCE_DIR}/smtsolvers
    ${CMAKE_SOURCE_DIR}/parsers/smt2new
    ${CMAKE_SOURCE_DIR}/simplifiers
    ${CMAKE_SOURCE_DIR}/proof
    ${GMP_INCLUDE_DIR}
)

if (ITP_DEBUG)
    add_definitions(-DITP_DEBUG)
endif (ITP_DEBUG)

if (PEDANTIC_DEBUG)
    add_definitions(-DPEDANTIC_DEBUG)
endif(PEDANTIC_DEBUG)

if(DEBUG_REASONS)
    add_definitions(-DDEBUG_REASONS)
endif()

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

if (USE_READLINE)
  add_definitions(-DUSE_READLINE)
endif()

add_subdirectory(${CMAKE_SOURCE_DIR})

################# TESTING #############################################
option(PACKAGE_TESTS "Build the tests" ON)
if(PACKAGE_TESTS)
    if(CMAKE_VERSION VERSION_LESS 3.11)
        MESSAGE(WARNING "Minimum CMAKE version for building tests is 3.11")
    else(CMAKE_VERSION VERSION_LESS 3.11)
        enable_testing()
        add_subdirectory(${PROJECT_SOURCE_DIR}/test)
    endif(CMAKE_VERSION VERSION_LESS 3.11)
endif()
#########################################################################
install(FILES ${CMAKE_SOURCE_DIR}/opensmt2.h DESTINATION ${INSTALL_HEADERS_DIR})

if (USE_READLINE)
  message("You have chosen to build OpenSMT against optional GPL-licensed components (readline)."
          "\n"
          "As these libraries are covered under the GPL, so will the resulting binary of OpenSMT.")
endif()

