add_library(api SHARED "")

target_sources(api
	PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/Interpret.h"
	PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/Interpret.C"
	PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/MainSolver.C"
	PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/MainSolver.h"
	PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/DimacsParser.h"
	PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/smt2tokens.h"
	PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/Opensmt.C"
)

target_include_directories(api
PUBLIC "${CMAKE_SOURCE_DIR}/smtsolvers"
PUBLIC "${CMAKE_SOURCE_DIR}"
)

find_package(Readline REQUIRED)
find_package(ZLIB REQUIRED)

target_link_libraries(api ${Readline_LIBRARY} ${ZLIB_LIBRARIES})

target_link_libraries(api -v -all_load smtsolvers parsers)

set_target_properties(api PROPERTIES OUTPUT_NAME opensmt2)

install(TARGETS api DESTINATION lib)

install(FILES Opensmt.h smt2tokens.h MainSolver.h 
DESTINATION ${INSTALL_HEADERS_DIR})

