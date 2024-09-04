target_sources(tsolvers
PRIVATE
    "${CMAKE_CURRENT_LIST_DIR}/LAVar.h"
    "${CMAKE_CURRENT_LIST_DIR}/LAVarMapper.cc"
    "${CMAKE_CURRENT_LIST_DIR}/Tableau.cc"
    "${CMAKE_CURRENT_LIST_DIR}/LABounds.cc"
    "${CMAKE_CURRENT_LIST_DIR}/Delta.cc"
    "${CMAKE_CURRENT_LIST_DIR}/LAVar.cc"
    "${CMAKE_CURRENT_LIST_DIR}/Polynomial.h"
    "${CMAKE_CURRENT_LIST_DIR}/Tableau.h"
    "${CMAKE_CURRENT_LIST_DIR}/LAVarMapper.h"
    "${CMAKE_CURRENT_LIST_DIR}/LARefs.h"
    "${CMAKE_CURRENT_LIST_DIR}/LABounds.h"
    "${CMAKE_CURRENT_LIST_DIR}/LRAModel.h"
    "${CMAKE_CURRENT_LIST_DIR}/LRAModel.cc"
    "${CMAKE_CURRENT_LIST_DIR}/Delta.h"
    "${CMAKE_CURRENT_LIST_DIR}/LASolver.h"
    "${CMAKE_CURRENT_LIST_DIR}/LASolver.cc"
    "${CMAKE_CURRENT_LIST_DIR}/Simplex.h"
    "${CMAKE_CURRENT_LIST_DIR}/Simplex.cc"
    "${CMAKE_CURRENT_LIST_DIR}/FarkasInterpolator.h"
    "${CMAKE_CURRENT_LIST_DIR}/FarkasInterpolator.cc"
    "${CMAKE_CURRENT_LIST_DIR}/SparseMatrix.cc"
    "${CMAKE_CURRENT_LIST_DIR}/LIAInterpolator.h"
    "${CMAKE_CURRENT_LIST_DIR}/LIAInterpolator.cc"
    "${CMAKE_CURRENT_LIST_DIR}/CutCreator.cc"
)

option(SIMPLEX_DEBUG "Deeper debugging of Simplex" OFF)

if (SIMPLEX_DEBUG)
    add_definitions(-DSIMPLEX_DEBUG)
endif (SIMPLEX_DEBUG)
