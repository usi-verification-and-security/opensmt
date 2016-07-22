#add_library(libheuristic Settings.cpp)

#target_link_libraries(libheuristic hiredis Lib)

add_executable(clause_server main.cpp Settings.cpp ClauseServer.cpp ServerThread.cpp)

target_link_libraries(clause_server Lib)

#set_target_properties(heuristic PROPERTIES
 #       COMPILE_FLAGS "-Wall -std=c++11 -g -gdwarf-2"
  #      )