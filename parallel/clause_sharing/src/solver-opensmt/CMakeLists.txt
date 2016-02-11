set(solver_opensmt_flags "-DIGNORE_DL_THEORYPROPAGATION -DOPTIMIZE -DNDEBUG -DOSMT1_SUBSTITUTION -DCUSTOM_EL_ALLOC -DTERMS_HAVE_EXPLANATIONS -DUSE_GZ -w -lz -lgmpxx -lgmp -lreadline -ltermcap")

find_package(GMP REQUIRED)
include_directories("${GMP_INCLUDE_DIR}")
link_directories("${GMP_LIBRARY_DIR}")

add_library(opensmt STATIC IMPORTED)
set_target_properties(opensmt PROPERTIES
        IMPORTED_LOCATION ${SRC_OPENSMT}/.libs/libopensmt.a
        )

add_library(solver Settings.cpp Solver.cpp)
set_target_properties(solver PROPERTIES
        COMPILE_FLAGS ${solver_opensmt_flags}
        )

add_executable(solver_opensmt main.cpp)

target_link_libraries(solver Lib hiredis opensmt ${solver_opensmt_flags})
target_link_libraries(solver_opensmt solver)