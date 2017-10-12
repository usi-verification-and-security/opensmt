add_library(pterms STATIC "")

target_include_directories(pterms 
	PRIVATE "${CMAKE_SOURCE_DIR}/common"
	PUBLIC "${CMAKE_SOURCE_DIR}/symbols"
)

target_sources(pterms
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/PtStore.h"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/Pterm.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/PtStore.C"
)

target_link_libraries(pterms symbols)
