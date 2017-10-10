add_library(symbols STATIC SymStore.C)

target_include_directories(symbols
	PRIVATE ${CMAKE_SOURCE_DIR}/common
	PUBLIC ${CMAKE_SOURCE_DIR}/sorts
)

target_link_libraries(symbols sorts)
