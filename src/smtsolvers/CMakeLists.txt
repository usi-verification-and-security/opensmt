add_library(smtsolvers OBJECT "")

target_sources(smtsolvers
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/SMTSolver.h"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/SimpSMTSolver.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/SimpSMTSolver.C"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/CoreSMTSolver.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/CoreSMTSolver.C"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/Theory.C"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/TheoryInterpolator.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/Debug.C"
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

if(COMPRESS)
	target_compile_definitions(smtsolvers PRIVATE -DUSE_GZ)
endif()

if(PRINT_DECOMPOSED_STATS)
    target_compile_definitions(smtsolvers PRIVATE -DPRINT_DECOMPOSED_STATS)
endif()

if(PRODUCE_PROOF)
	target_sources(proof
	PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/Proof.h"
	PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/Proof.C"
	)
	install(FILES TheoryInterpolator.h
			DESTINATION ${INSTALL_HEADERS_DIR})

endif()

install(FILES SimpSMTSolver.h CoreSMTSolver.h SMTSolver.h 
DESTINATION ${INSTALL_HEADERS_DIR})

