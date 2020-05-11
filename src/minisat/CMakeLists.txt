add_library(minisat INTERFACE)

target_include_directories(minisat
    INTERFACE ${CMAKE_CURRENT_LIST_DIR}/mtl
    INTERFACE ${CMAKE_CURRENT_LIST_DIR}/core
    )


install(FILES 
mtl/Heap.h mtl/Map.h mtl/Vec.h mtl/Alg.h mtl/Sort.h mtl/Queue.h core/SolverTypes.h
 DESTINATION ${INSTALL_HEADERS_DIR})

