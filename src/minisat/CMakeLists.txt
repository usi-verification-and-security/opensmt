add_library(minisat INTERFACE)

target_include_directories(minisat
INTERFACE "${CMAKE_CURRENT_SOURCE_DIR}/core"
INTERFACE "${CMAKE_CURRENT_SOURCE_DIR}/mtl"
)

include(core/CMakeLists.txt)
#include(mtl/CMakeLists.txt)
#include(utils/CMakeLists.txt)
#include(simp/CMakeLists.txt)
