add_library(tsolvers OBJECT "")

target_sources(tsolvers
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/Deductions.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/Deductions.cc"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/TSolverHandler.h"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/TSolver.h"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/TResult.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/CUFTHandler.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/LRATHandler.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/IDLTHandler.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/RDLTHandler.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/LIATHandler.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/THandler.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/TSolverHandler.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/UFLRATHandler.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/UFTHandler.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/TSolver.cc"
)

if(VERBOSE_EUF)
    target_compile_definitions(tsolvers PRIVATE -DVERBOSE_EUF)
endif()

if(VERBOSE_EUFEX)
    target_compile_definitions(tsolvers PRIVATE -DVERBOSE_EUFEX)
endif()

include(egraph/CMakeLists.txt)
include(lasolver/CMakeLists.txt)
include(lrasolver/CMakeLists.txt)
include(bvsolver/CMakeLists.txt)
include(liasolver/CMakeLists.txt)
include(stpsolver/CMakeLists.txt)

install(FILES Deductions.h UFTHandler.h CUFTHandler.h LRATHandler.h LIATHandler.h IDLTHandler.h RDLTHandler.h TSolver.h THandler.h
TSolverHandler.h TResult.h
DESTINATION ${INSTALL_HEADERS_DIR})

