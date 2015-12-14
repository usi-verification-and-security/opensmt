find_package(Threads REQUIRED)

add_library(Lib Frame.cpp Message.cpp Thread.cpp Process.cpp)

target_link_libraries(Lib ${CMAKE_THREAD_LIBS_INIT})