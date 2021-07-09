add_library(smtsolvers OBJECT "" LookaheadSMTSolver.cc LookaheadSMTSolver.h LookaheadSplitter.cc LookaheadSplitter.h LAScore.h LAScore.cc)

target_sources(smtsolvers
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/SMTSolver.h"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/SimpSMTSolver.h"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/GhostSMTSolver.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/SimpSMTSolver.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/CoreSMTSolver.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/CoreSMTSolver.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/GhostSMTSolver.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/TheoryIF.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/TheoryInterpolator.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/Debug.cc"
)

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


install(FILES SimpSMTSolver.h CoreSMTSolver.h SMTSolver.h 
DESTINATION ${INSTALL_HEADERS_DIR})

