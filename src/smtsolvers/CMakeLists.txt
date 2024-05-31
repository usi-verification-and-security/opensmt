add_library(smtsolvers OBJECT "")

list(APPEND PRIVATE_SOURCES_TO_ADD
		"${CMAKE_CURRENT_SOURCE_DIR}/SimpSMTSolver.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/CoreSMTSolver.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/GhostSMTSolver.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/TheoryIF.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/TheoryInterpolator.h"
		"${CMAKE_CURRENT_SOURCE_DIR}/Debug.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/LookaheadSMTSolver.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/LookaheadSMTSolver.h"
		"${CMAKE_CURRENT_SOURCE_DIR}/LAScore.h"
		"${CMAKE_CURRENT_SOURCE_DIR}/LAScore.cc"
		)
list(APPEND PUBLIC_SOURCES_TO_ADD
		"${CMAKE_CURRENT_SOURCE_DIR}/SimpSMTSolver.h"
		"${CMAKE_CURRENT_SOURCE_DIR}/GhostSMTSolver.h"
		"${CMAKE_CURRENT_SOURCE_DIR}/CoreSMTSolver.h"
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
	PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/ResolutionProof.h"
	PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/ResolutionProof.cc")

install(FILES TheoryInterpolator.h SimpSMTSolver.h CoreSMTSolver.h
	 DESTINATION ${INSTALL_HEADERS_DIR})