add_library(common OBJECT "FastRational.cc" Real.h)

target_sources(common
    PUBLIC "${CMAKE_CURRENT_LIST_DIR}/FastRational.h"
    PUBLIC "${CMAKE_CURRENT_LIST_DIR}/FlaPartitionMap.cc"
    PRIVATE
    "${CMAKE_CURRENT_LIST_DIR}/Alloc.h"
    "${CMAKE_CURRENT_LIST_DIR}/XAlloc.h"
    "${CMAKE_CURRENT_LIST_DIR}/SystemQueries.h"
    "${CMAKE_CURRENT_LIST_DIR}/Integer.h"
    "${CMAKE_CURRENT_LIST_DIR}/Number.h"
    "${CMAKE_CURRENT_LIST_DIR}/NumberUtils.h"
    "${CMAKE_CURRENT_LIST_DIR}/osmtinttypes.h"
    "${CMAKE_CURRENT_LIST_DIR}/StringMap.h"
    "${CMAKE_CURRENT_LIST_DIR}/StringConv.h"
    "${CMAKE_CURRENT_LIST_DIR}/Timer.h"
    "${CMAKE_CURRENT_LIST_DIR}/TreeOps.h"
    "${CMAKE_CURRENT_LIST_DIR}/NatSet.h"
    "${CMAKE_CURRENT_LIST_DIR}/PartitionInfo.cc"
    "${CMAKE_CURRENT_LIST_DIR}/VerificationUtils.cc"
    "${CMAKE_CURRENT_LIST_DIR}/ReportUtils.h"
)

install(FILES
        Integer.h Number.h FastRational.h XAlloc.h Alloc.h StringMap.h Timer.h osmtinttypes.h
        TreeOps.h Real.h FlaPartitionMap.h PartitionInfo.h OsmtApiException.h TypeUtils.h
        NumberUtils.h NatSet.h OsmtInternalException.h
DESTINATION ${INSTALL_HEADERS_DIR})


