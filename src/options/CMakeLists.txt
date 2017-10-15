add_library(options STATIC SMTConfig.C)

target_include_directories(options
	PUBLIC ${CMAKE_SOURCE_DIR}/common
	PUBLIC ${CMAKE_SOURCE_DIR}/minisat/mtl
	PUBLIC ${CMAKE_SOURCE_DIR}/minisat/core
	PUBLIC ${CMAKE_SOURCE_DIR}/api
)

install(FILES SMTConfig.h DESTINATION ${INSTALL_HEADERS_DIR})
