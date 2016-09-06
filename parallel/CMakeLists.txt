cmake_minimum_required(VERSION 3.2)

project(clause_server C CXX)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})

set(CMAKE_CXX_COMPILER "g++")

if (NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE "Release")
endif ()

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11 -Wall")
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -O0")

#if ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
#   # require at least gcc 4.8
#  if (CMAKE_CXX_COMPILER_VERSION VERSION_LESS 4.8)
#     message(FATAL_ERROR "GCC version must be at least 4.8! Found ${CMAKE_CXX_COMPILER} ${CMAKE_CXX_COMPILER_VERSION}")
#endif ()
#elseif ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang")
#    # require at least clang 3.2
#    if (CMAKE_CXX_COMPILER_VERSION VERSION_LESS 3.2)
#        message(FATAL_ERROR "Clang version must be at least 3.2!")
#    endif()
#else ()
#   message(WARNING "You are using an unsupported compiler! Compilation has only been tested with Clang and GCC.")
#endif ()

function(find NAME INCLUDE_NAMES LIBRARY_NAMES)
    if (NOT ${NAME}_INCLUDE_DIR)
        find_path(${NAME}_INCLUDE_DIR NAMES ${INCLUDE_NAMES}
                PATHS ${${NAME}_PATH}/include)
    endif ()

    if (NOT ${NAME}_LIBRARY)
        find_library(${NAME}_LIBRARY NAMES ${LIBRARY_NAMES}
                PATHS ${${NAME}_PATH}/lib)
    endif ()

    if (${NAME}_INCLUDE_DIR AND ${NAME}_LIBRARY)
        get_filename_component(${NAME}_LIBRARY_DIR ${${NAME}_LIBRARY} PATH)
        set(${NAME}_FOUND TRUE)
    endif ()

    if (${NAME}_FOUND)
        message(STATUS "Using ${NAME}_INCLUDE_DIR: ${${NAME}_INCLUDE_DIR}")
        message(STATUS "Using ${NAME}_LIBRARY: ${${NAME}_LIBRARY}")
        set(${NAME}_FOUND TRUE PARENT_SCOPE)
    elseif (${NAME}_FIND_REQUIRED)
        message(FATAL_ERROR "\nCould not find ${NAME}:\n"
                "Hint path using -D${NAME}_PATH=\n"
                "Or -D${NAME}_INCLUDE_DIR= and -D${NAME}_LIBRARY=\n")
    endif ()
endfunction()

include_directories("src")

add_subdirectory(src/contrib)
add_subdirectory(src/lib)
add_subdirectory(src/lemma_server)
add_subdirectory(src/client)

message(STATUS "CMAKE_BUILD_TYPE selected to ${CMAKE_BUILD_TYPE}")