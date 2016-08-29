add_library(client Settings.cpp FileThread.cpp SolverServer.cpp SolverProcess.cpp)
target_link_libraries(client Lib)

add_subdirectory(OpenSMT2)
#add_subdirectory(Z3)