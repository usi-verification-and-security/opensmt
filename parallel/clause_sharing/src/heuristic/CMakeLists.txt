add_library(libheuristic ClauseSharing.cpp)

target_link_libraries(libheuristic hiredis Lib)

add_executable(heuristic main.cpp)

target_link_libraries(heuristic libheuristic)