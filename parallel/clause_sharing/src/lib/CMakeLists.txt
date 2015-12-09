find_package(Threads REQUIRED)

add_library(Frame Frame.h)
add_library(Protocol Protocol.cpp)
add_library(Thread Thread.cpp)

target_link_libraries(Thread ${CMAKE_THREAD_LIBS_INIT})
set_target_properties(Frame PROPERTIES LINKER_LANGUAGE CXX)