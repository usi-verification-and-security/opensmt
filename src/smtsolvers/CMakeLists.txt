add_library(smtsolvers OBJECT "")

if(PARALLEL)
	set(PRIVATE_SOURCES_TO_ADD "${CMAKE_CURRENT_SOURCE_DIR}/ParallelScatterSplitter.cc")
	set(PUBLIC_SOURCES_TO_ADD "${CMAKE_CURRENT_SOURCE_DIR}/ParallelScatterSplitter.h")
endif()

list(APPEND PRIVATE_SOURCES_TO_ADD
		"${CMAKE_CURRENT_SOURCE_DIR}/SimpSMTSolver.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/CoreSMTSolver.h"
		"${CMAKE_CURRENT_SOURCE_DIR}/CoreSMTSolver.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/ScatterSplitter.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/SplitData.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/GhostSMTSolver.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/TheoryIF.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/TheoryInterpolator.h"
		"${CMAKE_CURRENT_SOURCE_DIR}/Debug.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/LookaheadSMTSolver.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/LookaheadSMTSolver.h"
		"${CMAKE_CURRENT_SOURCE_DIR}/LookaheadSplitter.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/LookaheadSplitter.h"
		"${CMAKE_CURRENT_SOURCE_DIR}/SplitContext.h"
		"${CMAKE_CURRENT_SOURCE_DIR}/LAScore.h"
		"${CMAKE_CURRENT_SOURCE_DIR}/LAScore.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/Splitter.h"
)
list(APPEND PUBLIC_SOURCES_TO_ADD
		"${CMAKE_CURRENT_SOURCE_DIR}/SimpSMTSolver.h"
		"${CMAKE_CURRENT_SOURCE_DIR}/GhostSMTSolver.h"
		"${CMAKE_CURRENT_SOURCE_DIR}/ScatterSplitter.h"
		"${CMAKE_CURRENT_SOURCE_DIR}/SplitData.h"
)

target_sources(smtsolvers PRIVATE ${PRIVATE_SOURCES_TO_ADD}  PUBLIC ${PUBLIC_SOURCES_TO_ADD} )

if(VERBOSE_SAT)
	target_compile_definitions(smtsolvers PRIVATE -DVERBOSE_SAT)
endif()

if(DEBUG_LOOKAHEAD)
	target_compile_definitions(smtsolvers PRIVATE -DLADEBUG)
endif()

if(PRINT_UNITS)
	target_compile_definitions(smtsolvers PRIVATE -DREPORT_DL1_THLITS)
endif()

target_sources(proof
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/Proof.h"
    PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/Proof.cc"
)
install(FILES TheoryInterpolator.h
        DESTINATION ${INSTALL_HEADERS_DIR})


install(FILES SimpSMTSolver.h CoreSMTSolver.h ScatterSplitter.h
DESTINATION ${INSTALL_HEADERS_DIR})

if(PARALLEL)
	install(FILES ParallelScatterSplitter.h DESTINATION ${INSTALL_HEADERS_DIR})
	target_link_libraries(smtsolvers PUBLIC PTPLib::PTPLib)
	target_compile_definitions(smtsolvers PUBLIC -DCUBE_AND_CONQUER)
endif(PARALLEL)