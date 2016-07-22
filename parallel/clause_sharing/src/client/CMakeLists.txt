add_library(client Settings.cpp ClauseThread.cpp FileThread.cpp SolverServer.cpp)
target_link_libraries(client Lib)

add_subdirectory(OpenSMT2)