find_package(Threads REQUIRED)

add_library(clause_sharing ClauseSharing.cpp)

target_link_libraries(clause_sharing ${CMAKE_THREAD_LIBS_INIT})
target_link_libraries(clause_sharing hiredis)
target_link_libraries(clause_sharing settings)
target_link_libraries(clause_sharing protocol)