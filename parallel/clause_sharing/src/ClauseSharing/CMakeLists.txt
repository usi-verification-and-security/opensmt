add_library(ClauseSharing ClauseSharing.cpp)
add_library(Protocol protocol.C)

target_link_libraries(ClauseSharing hiredis)
target_link_libraries(ClauseSharing Thread)
target_link_libraries(ClauseSharing Protocol)