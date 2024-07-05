cmake_minimum_required(VERSION 3.12)
project(opensmt-examples)

set(CMAKE_CXX_STANDARD 17)

set(OpenSMT_DIR CACHE PATH "Path to OpenSMT installation directory")

find_package(OpenSMT REQUIRED CONFIG
    PATHS ${OpenSMT_DIR})

file(GLOB_RECURSE my_c_list RELATIVE ${CMAKE_CURRENT_LIST_DIR} "*.cc")

foreach(file_path ${my_c_list})
    string( REPLACE ".cc" "" new_name ${file_path} )
    get_filename_component(filename ${new_name} NAME)
    add_executable( ${filename} ${file_path} )
    target_link_libraries(${filename} OpenSMT::OpenSMT)
endforeach()
