set(SRC_OPENSMT ${SRC}/../../../src)

include_directories(
        "${SRC_OPENSMT}"
        "${SRC_OPENSMT}/minisat/core"
        "${SRC_OPENSMT}/minisat/mtl"
        "${SRC_OPENSMT}/common"
        "${SRC_OPENSMT}/logics"
        "${SRC_OPENSMT}/options"
        "${SRC_OPENSMT}/symbols"
        "${SRC_OPENSMT}/api"
        "${SRC_OPENSMT}/pterms"
        "${SRC_OPENSMT}/sorts"
        "${SRC_OPENSMT}/smtsolvers"
        "${SRC_OPENSMT}/tsolvers"
        "${SRC_OPENSMT}/cnfizers"
        "${SRC_OPENSMT}/tsolvers/egraph"
        "${SRC_OPENSMT}/tsolvers/lrasolver"
        "${SRC_OPENSMT}/parsers/smt2new"
)

set(solver_opensmt_flags "-DIGNORE_DL_THEORYPROPAGATION -DOPTIMIZE -DNDEBUG -DOSMT1_SUBSTITUTION -DCUSTOM_EL_ALLOC -DTERMS_HAVE_EXPLANATIONS -DUSE_GZ -w -lz -lgmpxx -lgmp -lreadline -ltermcap -L/usr/local/opt/gmp/lib/")

find_package(GMP REQUIRED)
include_directories("${GMP_INCLUDE_DIR}")
link_directories("${GMP_LIBRARY_DIR}")

add_library(opensmt STATIC IMPORTED)
set_target_properties(opensmt PROPERTIES
        IMPORTED_LOCATION ${SRC_OPENSMT}/.libs/libopensmt.a
        )

#add_library(solver Settings.cpp Solver.cpp)
#set_target_properties(solver PROPERTIES
#        COMPILE_FLAGS ${solver_opensmt_flags}
#        )

add_executable(solver_opensmt main.cpp Settings.cpp SolverProcess.cpp ClauseThread.cpp SolverServer.cpp FileThread.cpp)
set_target_properties(solver_opensmt PROPERTIES
        COMPILE_FLAGS ${solver_opensmt_flags}
        )

target_link_libraries(solver_opensmt Lib opensmt ${solver_opensmt_flags})