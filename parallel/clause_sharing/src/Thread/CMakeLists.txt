find_package(Threads REQUIRED)

add_library(Thread Thread.cpp)

target_link_libraries(Thread ${CMAKE_THREAD_LIBS_INIT})