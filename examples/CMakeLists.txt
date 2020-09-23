cmake_minimum_required(VERSION 3.3)
project(opensmt-examples)

set(CMAKE_CXX_STANDARD 11)

#FIND OpenSMT library

if(OPENSMT_DIR)
    find_path(OPENSMT_INCLUDE_DIR NAMES "opensmt/opensmt2.h"
        PATHS ${OPENSMT_DIR}
        PATH_SUFFIXES "" "include" NO_DEFAULT_PATH
        )
    find_library(OPENSMT_LIBRARY NAMES opensmt
        PATHS ${OPENSMT_DIR}
        PATH_SUFFIXES "" "lib" "lib64" NO_DEFAULT_PATH
        )
else()
    message(FATAL_ERROR "\nProvide path to OpenSMT directory in OPENSMT_DIR\n")
endif(OPENSMT_DIR)

if(OPENSMT_INCLUDE_DIR)
    message(STATUS "OpenSMT include directory located: ${OPENSMT_INCLUDE_DIR}")
else()
    message(FATAL_ERROR "\nOpenSMT include directory could not be found in the provided directory\n")
endif(OPENSMT_INCLUDE_DIR)

if(OPENSMT_LIBRARY)
    message(STATUS "OpenSMT library located: ${OPENSMT_LIBRARY}")
else()
    message(FATAL_ERROR "\nOpenSMT library could not be found in the provided directory\n")
endif(OPENSMT_LIBRARY)

#find GMP
get_filename_component(CMAKE_MODULE_PATH
    "${CMAKE_CURRENT_LIST_DIR}/../cmake_modules/" ABSOLUTE)

find_package(GMP REQUIRED)

file(GLOB_RECURSE my_c_list RELATIVE ${CMAKE_CURRENT_LIST_DIR} "*.cc")

foreach(file_path ${my_c_list})
    string( REPLACE ".cc" "" new_name ${file_path} )
    get_filename_component(filename ${new_name} NAME)
    add_executable( ${filename} ${file_path} )
    target_include_directories(${filename} PUBLIC ${OPENSMT_INCLUDE_DIR} ${GMP_INCLUDE_DIR})
    target_link_libraries(${filename} ${OPENSMT_LIBRARY} ${GMP_LIBRARIES} ${GMPXX_LIBRARIES})
endforeach()
