cmake_minimum_required(VERSION 3.3)
project(opensmt-examples)

set(CMAKE_CXX_STANDARD 11)

get_filename_component(CMAKE_MODULE_PATH
    "${CMAKE_CURRENT_LIST_DIR}/../cmake_modules/" ABSOLUTE)

set(opensmt_DIR CACHE PATH "Path to OpenSMT installation directry")

find_package(opensmt REQUIRED CONFIG
    PATHS ${opensmt_DIR})

file(GLOB_RECURSE my_c_list RELATIVE ${CMAKE_CURRENT_LIST_DIR} "*.cc")

foreach(file_path ${my_c_list})
    string( REPLACE ".cc" "" new_name ${file_path} )
    get_filename_component(filename ${new_name} NAME)
    add_executable( ${filename} ${file_path} )
    target_link_libraries(${filename} opensmt::opensmt)
endforeach()
