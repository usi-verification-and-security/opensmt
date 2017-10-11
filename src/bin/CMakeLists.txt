add_executable(exec opensmt.C)

set(THREADS_PREFER_PTHREAD_FLAG ON)
find_package(Threads REQUIRED)
target_link_libraries(exec Threads::Threads)

target_link_libraries(exec api)
