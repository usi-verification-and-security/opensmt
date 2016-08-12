find_package(Threads REQUIRED)

add_library(Lib
        lib.cpp
        Thread.cpp
        Process.cpp
        Log.h
        net/Address.cpp
        net/Pipe.cpp
        net/Server.cpp
        net/Socket.cpp
        )

target_link_libraries(Lib ${CMAKE_THREAD_LIBS_INIT})