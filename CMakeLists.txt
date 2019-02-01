cmake_minimum_required(VERSION 3.3)
project(opensmt)

set(CMAKE_CXX_STANDARD 11)

set(CMAKE_SOURCE_DIR "src")

get_filename_component(CMAKE_MODULE_PATH
"${CMAKE_SOURCE_DIR}/../cmake_modules/" ABSOLUTE)

set(CMAKE_POSITION_INDEPENDENT_CODE ON)

#message(${CMAKE_C_COMPILER_ID})
#message(${CMAKE_CXX_COMPILER_ID})

set(INSTALL_HEADERS_DIR include/opensmt)

option(PRODUCE_PROOF "Produce proof" OFF)
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
#option(ENABLE_PROFILING "Enable profiling" OFF)

find_package(Readline REQUIRED)
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

# there should be a better way of profiling
#if(ENABLE_PROFILING)
#    add_compile_options(-pg)
#endif()

if (PRODUCE_PROOF)
    add_definitions(-DPRODUCE_PROOF -DFULL_LABELING)
    include_directories(${CMAKE_SOURCE_DIR}/proof)
endif ()

if (LADEBUG)
    add_definitions(-DLADEBUG)
endif ()

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
