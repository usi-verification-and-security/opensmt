add_library(api STATIC "")

target_sources(api
	PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/Interpret.h"
	PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/Interpret.C"
	PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/MainSolver.C"
	PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/MainSolver.h"
)

target_include_directories(api
PUBLIC "${CMAKE_SOURCE_DIR}/smtsolvers"
PUBLIC "${CMAKE_SOURCE_DIR}"
)

find_package(Readline REQUIRED)

target_link_libraries(api ${Readline_LIBRARY})

target_link_libraries(api smtsolvers parsers)
