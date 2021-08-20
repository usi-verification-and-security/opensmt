cmake_minimum_required(VERSION 3.3)
project(opensmt-examples)

set(CMAKE_CXX_STANDARD 17)

if (POLICY CMP0074) # Policy 0074 has been introduced in CMake 3.12, so we need a check, otherwise older version would give an error
cmake_policy(SET CMP0074 NEW)
endif()

set(OpenSMT_DIR CACHE PATH "Path to OpenSMT installation directry")

find_package(OpenSMT REQUIRED CONFIG
    PATHS ${OpenSMT_DIR})

file(GLOB_RECURSE my_c_list RELATIVE ${CMAKE_CURRENT_LIST_DIR} "*.cc")

foreach(file_path ${my_c_list})
    string( REPLACE ".cc" "" new_name ${file_path} )
    get_filename_component(filename ${new_name} NAME)
    add_executable( ${filename} ${file_path} )
    target_link_libraries(${filename} OpenSMT::OpenSMT)
endforeach()
