add_library(minisat INTERFACE)

install(FILES 
        mtl/Heap.h
        mtl/Map.h
        mtl/Vec.h
        mtl/Alg.h
        mtl/Sort.h
        mtl/Queue.h
        mtl/MapWithKeys.h
        DESTINATION ${INSTALL_HEADERS_DIR}/minisat/mtl
)

install(FILES
        core/SolverTypes.h
        core/Alloc.h
        core/XAlloc.h
        DESTINATION ${INSTALL_HEADERS_DIR}/minisat/core)


