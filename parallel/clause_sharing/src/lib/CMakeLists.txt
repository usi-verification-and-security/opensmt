find_package(Threads REQUIRED)

add_library(Lib Thread.cpp Process.cpp Net.cpp Log.h)

target_link_libraries(Lib ${CMAKE_THREAD_LIBS_INIT})