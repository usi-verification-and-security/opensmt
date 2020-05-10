target_sources(tsolvers
PUBLIC "${CMAKE_CURRENT_LIST_DIR}/Egraph.h"
PUBLIC "${CMAKE_CURRENT_LIST_DIR}/Enode.h"
PUBLIC "${CMAKE_CURRENT_LIST_DIR}/EnodeStore.h"
PUBLIC "${CMAKE_CURRENT_LIST_DIR}/CgTypes.h"

PRIVATE "${CMAKE_CURRENT_LIST_DIR}/Enode.cc"
PRIVATE "${CMAKE_CURRENT_LIST_DIR}/EnodeStore.cc"
PRIVATE "${CMAKE_CURRENT_LIST_DIR}/EgraphSolver.cc"
PRIVATE "${CMAKE_CURRENT_LIST_DIR}/EgraphExplain.cc"
PRIVATE "${CMAKE_CURRENT_LIST_DIR}/EgraphDebug.cc"
)

if(PRODUCE_PROOF)
	target_sources(tsolvers
		PUBLIC "${CMAKE_CURRENT_LIST_DIR}/UFInterpolator.h"
		PRIVATE "${CMAKE_CURRENT_LIST_DIR}/UFInterpolator.cc"
        PUBLIC "${CMAKE_CURRENT_LIST_DIR}/InterpolatingEgraph.h"
        PRIVATE "${CMAKE_CURRENT_LIST_DIR}/InterpolatingEgraph.cc"
	)

	install(FILES ${CMAKE_CURRENT_LIST_DIR}/UFInterpolator.h DESTINATION ${INSTALL_HEADERS_DIR})
endif()


