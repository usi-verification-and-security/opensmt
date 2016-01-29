add_library(libheuristic Settings.cpp Heuristic.cpp)

target_link_libraries(libheuristic hiredis Lib)

add_executable(heuristic main.cpp)

target_link_libraries(heuristic libheuristic)

#set_target_properties(heuristic PROPERTIES
 #       COMPILE_FLAGS "-Wall -std=c++11 -g -gdwarf-2"
  #      )