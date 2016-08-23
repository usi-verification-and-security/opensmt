find_package(Threads REQUIRED)

list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}")
find_package(SQLITE3 REQUIRED)
include_directories(${SQLITE3_INCLUDE_DIR})

add_library(Lib
        lib.cpp
        sqlite3.cpp
        Thread.cpp
        Process.cpp
        Log.h
        net/Address.cpp
        net/Pipe.cpp
        net/Server.cpp
        net/Socket.cpp
        )

target_link_libraries(Lib ${CMAKE_THREAD_LIBS_INIT} ${SQLITE3_LIBRARY})