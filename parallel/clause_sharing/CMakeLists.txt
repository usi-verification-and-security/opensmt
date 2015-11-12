cmake_minimum_required(VERSION 2.8)
project(clause_sharing)

set(OPENSMT ../..)
set(SRC ./src)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -g")


include_directories(
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

add_executable(heuristic ${SRC}/main.cpp)

target_link_libraries(heuristic hiredis)
target_link_libraries(heuristic protocol)
target_link_libraries(heuristic settings)