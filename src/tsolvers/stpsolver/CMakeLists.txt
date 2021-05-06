target_sources(tsolvers
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/STPSolver.h"
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/STPStore.h"
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/STPMapper.h"
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/STPEdgeGraph.h"
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/STPGraphManager.h"
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/STPModel.h"
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/SafeInt.h"
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/Converter.h"

    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/STPSolver_implementations.hpp"
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/STPStore_implementations.hpp"
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/STPMapper_implementations.hpp"
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/STPGraphManager_implementations.hpp"
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/STPModel_implementations.hpp"
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/STPEdgeGraph.cc"

    PUBLIC "${CMAKE_CURRENT_LIST_DIR}/IDLSolver.h"
    PUBLIC "${CMAKE_CURRENT_LIST_DIR}/RDLSolver.h"
    )
