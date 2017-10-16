add_library(sorts OBJECT SSort.C SStore.C)

target_include_directories(sorts
	PUBLIC ${CMAKE_SOURCE_DIR}/options
	PRIVATE ${CMAKE_SOURCE_DIR}/common
	PUBLIC ${CMAKE_SOURCE_DIR}/api #because of smt2tokens.h
)

#target_link_libraries(sorts PUBLIC minisat)

install(FILES SSort.h SStore.h DESTINATION ${INSTALL_HEADERS_DIR})

