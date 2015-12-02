cmake_minimum_required(VERSION 2.8)
project(clause_sharing C CXX)

set(OPENSMT ../..)
set(SRC ./src)

set(CMAKE_CXX_COMPILER "g++")

#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -g -gdwarf-2 -std=gnu++11")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=gnu++11")

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
add_subdirectory(${SRC}/clause_sharing)

add_executable(heuristic ${SRC}/main.cpp)

target_link_libraries(heuristic clause_sharing)