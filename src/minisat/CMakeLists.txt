add_library(minisat INTERFACE)

target_include_directories(minisat
INTERFACE "${CMAKE_CURRENT_SOURCE_DIR}/core"
INTERFACE "${CMAKE_CURRENT_SOURCE_DIR}/mtl"
)

include(core/CMakeLists.txt)
#include(mtl/CMakeLists.txt)
#include(utils/CMakeLists.txt)
#include(simp/CMakeLists.txt)

install(FILES 
mtl/Heap.h mtl/Map.h mtl/Vec.h mtl/Alg.h mtl/Sort.h mtl/Queue.h core/SolverTypes.h
 DESTINATION ${INSTALL_HEADERS_DIR})

