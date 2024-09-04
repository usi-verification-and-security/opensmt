target_sources(tsolvers
PUBLIC
    "${CMAKE_CURRENT_LIST_DIR}/BVStore.h"
    "${CMAKE_CURRENT_LIST_DIR}/BitBlaster.h"
    "${CMAKE_CURRENT_LIST_DIR}/Bvector.h"
PRIVATE
    "${CMAKE_CURRENT_LIST_DIR}/BVSolver.h"
    "${CMAKE_CURRENT_LIST_DIR}/BVSolver.cc"
    "${CMAKE_CURRENT_LIST_DIR}/BVStore.cc"
    "${CMAKE_CURRENT_LIST_DIR}/BitBlaster.cc"
    "${CMAKE_CURRENT_LIST_DIR}/BVSolver.cc"
)

install(FILES
${CMAKE_CURRENT_LIST_DIR}/BitBlaster.h
${CMAKE_CURRENT_LIST_DIR}/BVStore.h
${CMAKE_CURRENT_LIST_DIR}/Bvector.h
DESTINATION ${INSTALL_HEADERS_DIR}/tsolvers/bvsolver)
