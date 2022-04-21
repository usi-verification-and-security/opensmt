if(PARALLEL)
	set(splitter ParallelScatterSplitter)
else()
	set(splitter ScatterSplitter)
endif()

add_library(smtsolvers OBJECT "")

target_sources(smtsolvers
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/SimpSMTSolver.h"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/GhostSMTSolver.h"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/${splitter}.h"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/SplitData.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/SimpSMTSolver.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/CoreSMTSolver.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/CoreSMTSolver.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/${splitter}.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/SplitData.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/GhostSMTSolver.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/TheoryIF.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/TheoryInterpolator.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/Debug.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/LookaheadSMTSolver.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/LookaheadSMTSolver.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/LookaheadSplitter.cc"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/LookaheadSplitter.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/SplitContext.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/LAScore.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/LAScore.cc"
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


install(FILES SimpSMTSolver.h CoreSMTSolver.h ${splitter}.h
DESTINATION ${INSTALL_HEADERS_DIR})

if(PARALLEL)
	target_link_libraries(smtsolvers PUBLIC PTPLib::PTPLib)
	target_compile_definitions(smtsolvers PUBLIC -DCUBE_AND_CONQUER)
endif()