add_executable(solver_z3 ../main.cpp SolverProcess.cpp)

list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}")
find_package(Z3)
if (NOT Z3_FOUND)
    contrib(Z3 solver_z3)
    if (NOT (Z3_INCLUDE_DIR AND Z3_LIBRARY))
        find_package(Z3 REQUIRED)
    endif ()
endif ()

include_directories(${Z3_INCLUDE_DIR})
target_link_libraries(solver_z3 client ${Z3_LIBRARY})