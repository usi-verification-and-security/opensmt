add_library(common STATIC "FastRational.C")

find_package(GMP REQUIRED)
include_directories(${GMP_INCLUDE_DIR})
target_link_libraries(common ${GMP_LIBRARIES} ${GMPXX_LIBRARIES})

target_sources(common
PUBLIC "${CMAKE_CURRENT_LIST_DIR}/FastRational.h"
PRIVATE	
"${CMAKE_CURRENT_LIST_DIR}/Alloc.h"
"${CMAKE_CURRENT_LIST_DIR}/XAlloc.h"
"${CMAKE_CURRENT_LIST_DIR}/Global.h"
"${CMAKE_CURRENT_LIST_DIR}/IntTypes.h"
"${CMAKE_CURRENT_LIST_DIR}/Otl.h"
"${CMAKE_CURRENT_LIST_DIR}/SigMap.h"
"${CMAKE_CURRENT_LIST_DIR}/StringMap.h"
"${CMAKE_CURRENT_LIST_DIR}/Timer.h"
"${CMAKE_CURRENT_LIST_DIR}/TreeOps.h"
)
