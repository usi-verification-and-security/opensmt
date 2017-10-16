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

#target_link_libraries(smtsolvers sorts tsolvers)
if(PRODUCE_PROOF)
	target_sources(proof
	PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/Proof.h"
	PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/Proof.C"
	)
	target_include_directories(proof
	PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}"
	)
	target_include_directories(smtsolvers
	PUBLIC "${CMAKE_SOURCE_DIR}/proof"
	)
	#target_link_libraries(smtsolvers minisat proof)
	install(FILES TheoryInterpolator.h Proof.h DESTINATION ${INSTALL_HEADERS_DIR})

endif()

install(FILES SimpSMTSolver.h CoreSMTSolver.h SMTSolver.h 
DESTINATION ${INSTALL_HEADERS_DIR})

