add_library(symbols STATIC SymStore.C)

target_include_directories(symbols
	PRIVATE ${CMAKE_SOURCE_DIR}/common
	PUBLIC ${CMAKE_SOURCE_DIR}/sorts
)

target_sources(symbols
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/Symbol.h"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/SymStore.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/SymStore.C"
)

target_link_libraries(symbols sorts)

install(FILES Symbol.h SymStore.h DESTINATION ${INSTALL_HEADERS_DIR})

