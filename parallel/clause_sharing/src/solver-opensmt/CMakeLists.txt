add_library(libopensmt STATIC IMPORTED)
set_target_properties(libopensmt PROPERTIES
        IMPORTED_LOCATION ${SRC_OPENSMT}/.libs/libopensmt.a
        )

set(solver_opensmt_flags "-DIGNORE_DL_THEORYPROPAGATION -DOPTIMIZE -DNDEBUG -DOSMT1_SUBSTITUTION -DCUSTOM_EL_ALLOC -DTERMS_HAVE_EXPLANATIONS -DUSE_GZ -W -Wall -Wno-deprecated -lz -lgmpxx -lgmp -lpthread -lreadline -ltermcap -lpthread -ltermcap")

add_executable(solver_opensmt main.cpp)
set_target_properties(solver_opensmt PROPERTIES
        COMPILE_FLAGS ${solver_opensmt_flags}
        )

target_link_libraries(solver_opensmt libopensmt ${solver_opensmt_flags})