add_library(common STATIC "FastRational.C")

find_package(GMP REQUIRED)
include_directories(${GMP_INCLUDE_DIR})
target_link_libraries(common ${GMP_LIBRARIES} ${GMPXX_LIBRARIES})

target_sources(common
	PRIVATE
		"${CMAKE_CURRENT_LIST_DIR}/Alloc.h"
	PUBLIC
		"${CMAKE_CURRENT_LIST_DIR}/XAlloc.h"	
)
