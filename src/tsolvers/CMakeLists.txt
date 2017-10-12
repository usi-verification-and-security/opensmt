add_library(tsolvers STATIC "")

target_sources(tsolvers
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/Deductions.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/Deductions.C"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/TSolverHandler.h"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/TSolver.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/CUFTHandler.C"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/LRATHandler.C"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/THandler.C"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/TSolverHandler.C"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/UFLRATHandler.C"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/UFTHandler.C"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/TSolver.C"
)

target_include_directories(tsolvers
INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/egraph"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/lrasolver"
PUBLIC "${CMAKE_SOURCE_DIR}/simplifiers"
PUBLIC "${CMAKE_SOURCE_DIR}/pterms"
)

target_link_libraries(tsolvers cnfizers simplifiers)

include(egraph/CMakeLists.txt)
include(lrasolver/CMakeLists.txt)
include(bvsolver/CMakeLists.txt)
