add_executable(exec opensmt.C)

#get the sha1 of the last commit in git (current HEAD) and store it in a variable
execute_process(COMMAND git rev-parse HEAD OUTPUT_VARIABLE GIT_SHA1 OUTPUT_STRIP_TRAILING_WHITESPACE)
#message(${GIT_SHA1}) 

target_compile_definitions(exec PRIVATE GIT_SHA1="${GIT_SHA1}")

set(THREADS_PREFER_PTHREAD_FLAG ON)
find_package(Threads REQUIRED)
target_link_libraries(exec Threads::Threads)

target_link_libraries(exec api_static)

set_target_properties(exec PROPERTIES OUTPUT_NAME opensmt)
