cmake_minimum_required(VERSION 2.8)

project(clause_sharing C CXX)

set(CMAKE_CXX_COMPILER "g++")

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -std=c++11 -g -gdwarf-2")
#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -std=c++11")

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

set(OPENSMT ../..)
set(SRC ./src)

include_directories(
        "${SRC}"
        "${OPENSMT}/src/net/hiredis"
        "${OPENSMT}/src/minisat/core"
        "${OPENSMT}/src/minisat/mtl"
        "${OPENSMT}/src"
        "${OPENSMT}/src/common"
)

add_library(hiredis STATIC
        "${OPENSMT}/src/net/hiredis/hiredis.c"
        "${OPENSMT}/src/net/hiredis/async.c"
        "${OPENSMT}/src/net/hiredis/dict.c"
        "${OPENSMT}/src/net/hiredis/net.c"
        "${OPENSMT}/src/net/hiredis/sds.c"
        "${OPENSMT}/src/net/hiredis/read.c"
        )

add_library(protocol STATIC
        "${OPENSMT}/src/net/protocol.C"
        )

add_subdirectory(${SRC}/settings)
add_subdirectory(${SRC}/ClauseSharing)
add_subdirectory(${SRC}/Thread)

add_executable(heuristic ${SRC}/main.cpp)

target_link_libraries(heuristic ClauseSharing)
target_link_libraries(heuristic settings)