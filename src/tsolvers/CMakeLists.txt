add_library(tsolvers OBJECT)

target_sources(tsolvers
PUBLIC
    "${CMAKE_CURRENT_SOURCE_DIR}/Deductions.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/TSolverHandler.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/TResult.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/LATHandler.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/UFTHandler.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/IDLTHandler.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/RDLTHandler.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/TSolver.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/THandler.h"
PRIVATE
    "${CMAKE_CURRENT_SOURCE_DIR}/Deductions.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/IDLTHandler.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/RDLTHandler.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/LATHandler.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/THandler.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/TSolverHandler.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/UFLATHandler.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/UFTHandler.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/TSolver.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/ArrayTHandler.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/ArrayTHandler.cc"
)

include(egraph/CMakeLists.txt)
include(lasolver/CMakeLists.txt)
#include(bvsolver/CMakeLists.txt)
include(stpsolver/CMakeLists.txt)
include(arraysolver/CMakeLists.txt)

install(FILES Deductions.h UFTHandler.h LATHandler.h IDLTHandler.h RDLTHandler.h TSolver.h THandler.h
TSolverHandler.h TResult.h
DESTINATION ${INSTALL_HEADERS_DIR}/tsolvers)
