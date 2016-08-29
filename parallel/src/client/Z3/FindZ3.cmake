find_path(Z3_INCLUDE_DIR z3.h z3++.h
        PATHS ${Z3_PATH}/include)

find_library(Z3_LIBRARY NAMES z3
        PATHS ${Z3_PATH}/lib)


if (Z3_INCLUDE_DIR AND Z3_LIBRARY)
    get_filename_component(Z3_LIBRARY_DIR ${Z3_LIBRARY} PATH)
    set(Z3_FOUND TRUE)
else ()

endif ()

#set(Z3_REPO https://github.com/Z3Prover/z3)
#execute_process(COMMAND git clone ${Z3_REPO} z3
#        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
#        RESULT_VARIABLE Z3_GIT_RESULT
#        )

#message(${Z3_PATH})

#if (${Z3_GIT_RESULT} = 0)
#    message(FATAL_ERROR Failed to clone Z3)
#endif ()

if (Z3_FOUND)
    message(STATUS "Found Z3: ${Z3_LIBRARY}")
elseif (Z3_FIND_REQUIRED)
    message(FATAL_ERROR "Could not find Z3: use -DZ3_PATH=")
endif ()
