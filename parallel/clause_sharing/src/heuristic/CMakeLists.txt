#add_library(libheuristic Settings.cpp)

#target_link_libraries(libheuristic hiredis Lib)

add_executable(heuristic main.cpp Settings.cpp HeuriscticServer.cpp ServerThread.cpp)

target_link_libraries(heuristic Lib)

#set_target_properties(heuristic PROPERTIES
 #       COMPILE_FLAGS "-Wall -std=c++11 -g -gdwarf-2"
  #      )