cmake_minimum_required(VERSION 2.8)

project(clause_sharing C CXX)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})

set(CMAKE_CXX_COMPILER "g++")

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -std=c++11 -g -gdwarf-2")
#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -w -O3 -std=c++11")

#if ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
#   # require at least gcc 4.8
#  if (CMAKE_CXX_COMPILER_VERSION VERSION_LESS 4.8)
#     message(FATAL_ERROR "GCC version must be at least 4.8! Found ${CMAKE_CXX_COMPILER} ${CMAKE_CXX_COMPILER_VERSION}")
#endif ()
#elseif ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang")
#    # require at least clang 3.2
#    if (CMAKE_CXX_COMPILER_VERSION VERSION_LESS 3.2)
#        message(FATAL_ERROR "Clang version must be at least 3.2!")
#    endif()
#else ()
#   message(WARNING "You are using an unsupported compiler! Compilation has only been tested with Clang and GCC.")
#endif ()

set(SRC ${CMAKE_CURRENT_SOURCE_DIR}/src)
set(SRC_OPENSMT ${SRC}/../../../src)

set(CMAKE_MODULE_PATH "${SRC}")

include_directories(
        "${SRC}"
        "${SRC_OPENSMT}"
        "${SRC_OPENSMT}/minisat/core"
        "${SRC_OPENSMT}/minisat/mtl"
        "${SRC_OPENSMT}/common"
        "${SRC_OPENSMT}/logics"
        "${SRC_OPENSMT}/options"
        "${SRC_OPENSMT}/symbols"
        "${SRC_OPENSMT}/api"
        "${SRC_OPENSMT}/pterms"
        "${SRC_OPENSMT}/sorts"
        "${SRC_OPENSMT}/smtsolvers"
        "${SRC_OPENSMT}/tsolvers"
        "${SRC_OPENSMT}/cnfizers"
        "${SRC_OPENSMT}/tsolvers/egraph"
        "${SRC_OPENSMT}/tsolvers/lrasolver"
)

add_subdirectory(${SRC}/deps)
add_subdirectory(${SRC}/lib)
add_subdirectory(${SRC}/heuristic)
add_subdirectory(${SRC}/solver-opensmt)


#add_executable(main ${SRC}/main.cpp)
#target_link_libraries(main Lib)