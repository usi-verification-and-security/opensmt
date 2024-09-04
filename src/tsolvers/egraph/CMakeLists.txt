target_sources(tsolvers
PUBLIC
    "${CMAKE_CURRENT_LIST_DIR}/CgTypes.h"
PRIVATE
    "${CMAKE_CURRENT_LIST_DIR}/Egraph.h"
    "${CMAKE_CURRENT_LIST_DIR}/Enode.h"
    "${CMAKE_CURRENT_LIST_DIR}/EnodeStore.h"
    "${CMAKE_CURRENT_LIST_DIR}/InterpolatingEgraph.h"
    "${CMAKE_CURRENT_LIST_DIR}/UFInterpolator.h"
    "${CMAKE_CURRENT_LIST_DIR}/EgraphDebug.cc"
    "${CMAKE_CURRENT_LIST_DIR}/EgraphModelBuilder.cc"
    "${CMAKE_CURRENT_LIST_DIR}/EgraphSolver.cc"
    "${CMAKE_CURRENT_LIST_DIR}/Enode.cc"
    "${CMAKE_CURRENT_LIST_DIR}/EnodeStore.cc"
    "${CMAKE_CURRENT_LIST_DIR}/Explainer.cc"
    "${CMAKE_CURRENT_LIST_DIR}/InterpolatingEgraph.cc"
    "${CMAKE_CURRENT_LIST_DIR}/UFInterpolator.cc"
)

install(FILES
    ${CMAKE_CURRENT_LIST_DIR}/CgTypes.h
DESTINATION ${INSTALL_HEADERS_DIR}/tsolvers/egraph)
