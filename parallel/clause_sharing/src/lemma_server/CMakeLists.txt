#add_library(libheuristic Settings.cpp)

#target_link_libraries(libheuristic hiredis Lib)

add_executable(lemma_server main.cpp Settings.cpp LemmaServer.cpp ServerThread.cpp)

target_link_libraries(lemma_server Lib)

#set_target_properties(heuristic PROPERTIES
 #       COMPILE_FLAGS "-Wall -std=c++11 -g -gdwarf-2"
  #      )