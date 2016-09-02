include(ExternalProject)

list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}")
find_package(Z3)

#execute_process(COMMAND git clone ${Z3_REPO} z3
#        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
#        RESULT_VARIABLE Z3_GIT_RESULT
#        )
#
#if (${Z3_GIT_RESULT} = 0)
#    message(FATAL_ERROR Failed to clone Z3)
#endif ()

include_directories(${CMAKE_BINARY_DIR}/z3/include)

add_executable(solver_z3 ../main.cpp  SolverProcess.cpp)

target_link_libraries(solver_z3 client ${CMAKE_BINARY_DIR}/z3/lib/libz3.dylib)

ExternalProject_Add(z3
        SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/z3
        PATCH_COMMAND git clean -fx src && python contrib/cmake/bootstrap.py create
        UPDATE_COMMAND ""
        CMAKE_ARGS -DCMAKE_INSTALL_PREFIX=${CMAKE_BINARY_DIR}/z3
        )

