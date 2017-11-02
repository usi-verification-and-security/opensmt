add_library(minisat INTERFACE)

install(FILES 
mtl/Heap.h mtl/Map.h mtl/Vec.h mtl/Alg.h mtl/Sort.h mtl/Queue.h core/SolverTypes.h
 DESTINATION ${INSTALL_HEADERS_DIR})

