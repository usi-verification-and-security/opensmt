add_library(pterms STATIC PtStore.C)

target_include_directories(pterms 
	PRIVATE "${CMAKE_SOURCE_DIR}/common"
	PUBLIC "${CMAKE_SOURCE_DIR}/symbols"
	INTERFACE "${CMAKE_CURRENT_SOURCE_DIR}"
)

target_link_libraries(pterms symbols)
