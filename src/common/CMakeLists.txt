add_library(common OBJECT "FastRational.C" Real.h)

target_sources(common
PUBLIC "${CMAKE_CURRENT_LIST_DIR}/FastRational.h"
PRIVATE	
"${CMAKE_CURRENT_LIST_DIR}/Alloc.h"
"${CMAKE_CURRENT_LIST_DIR}/XAlloc.h"
"${CMAKE_CURRENT_LIST_DIR}/Global.h"
"${CMAKE_CURRENT_LIST_DIR}/IntTypes.h"
"${CMAKE_CURRENT_LIST_DIR}/SigMap.h"
"${CMAKE_CURRENT_LIST_DIR}/StringMap.h"
"${CMAKE_CURRENT_LIST_DIR}/Timer.h"
"${CMAKE_CURRENT_LIST_DIR}/TreeOps.h"
)

install(FILES 
    Global.h FastRational.h XAlloc.h Alloc.h StringMap.h SigMap.h Timer.h IntTypes.h Real.h
DESTINATION ${INSTALL_HEADERS_DIR})


