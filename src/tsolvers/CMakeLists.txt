add_library(tsolvers OBJECT "" lrasolver/Tableau.h lrasolver/Polynomial.h lrasolver/Tableau.cpp lrasolver/Polynomial.cpp)

target_sources(tsolvers
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/Deductions.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/Deductions.C"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/TSolverHandler.h"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/TSolver.h"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/TResult.h"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/LASolver.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/CUFTHandler.C"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/LRATHandler.C"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/LIATHandler.C"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/THandler.C"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/TSolverHandler.C"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/UFLRATHandler.C"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/UFTHandler.C"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/TSolver.C"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/LASolver.C"
)

if(VERBOSE_EUF)
    target_compile_definitions(tsolvers PRIVATE -DVERBOSE_EUF)
endif()

if(VERBOSE_EUFEX)
    target_compile_definitions(tsolvers PRIVATE -DVERBOSE_EUFEX)
endif()

include(egraph/CMakeLists.txt)
include(lrasolver/CMakeLists.txt)
include(bvsolver/CMakeLists.txt)
include(liasolver/CMakeLists.txt)

install(FILES Deductions.h UFTHandler.h CUFTHandler.h LRATHandler.h LIATHandler.h TSolver.h LASolver.h THandler.h
TSolverHandler.h TResult.h
DESTINATION ${INSTALL_HEADERS_DIR})

