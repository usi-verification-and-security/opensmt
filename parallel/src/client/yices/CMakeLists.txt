add_executable(solver_yices ../main.cpp SolverProcess.cpp)

list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}")
find_package(YICES)
if (NOT YICES_FOUND)
    contrib(YICES solver_yices)
    if (NOT (YICES_INCLUDE_DIR AND YICES_LIBRARY))
        find_package(YICES REQUIRED)
    endif ()
endif ()

include_directories(${YICES_INCLUDE_DIR})
target_link_libraries(solver_yices client ${YICES_LIBRARY})