add_library(tsolvers OBJECT "")

target_sources(tsolvers
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/Deductions.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/Deductions.cc"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/TSolverHandler.h"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/TSolver.h"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/TResult.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/IDLTHandler.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/RDLTHandler.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/LATHandler.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/THandler.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/TSolverHandler.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/UFLATHandler.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/UFTHandler.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/TSolver.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/ArrayTHandler.cc"
)

include(egraph/CMakeLists.txt)
include(lasolver/CMakeLists.txt)
include(bvsolver/CMakeLists.txt)
include(stpsolver/CMakeLists.txt)
include(arraysolver/CMakeLists.txt)

install(FILES Deductions.h UFTHandler.h LATHandler.h IDLTHandler.h RDLTHandler.h TSolver.h THandler.h
TSolverHandler.h TResult.h
DESTINATION ${INSTALL_HEADERS_DIR}/tsolvers)
