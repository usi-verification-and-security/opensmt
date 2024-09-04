add_library(common OBJECT)

target_sources(common
PUBLIC
    "${CMAKE_CURRENT_LIST_DIR}/FastRational.cc"
    "${CMAKE_CURRENT_LIST_DIR}/FlaPartitionMap.cc"
    "${CMAKE_CURRENT_LIST_DIR}/Real.h"
PRIVATE
    "${CMAKE_CURRENT_LIST_DIR}/SystemQueries.h"
    "${CMAKE_CURRENT_LIST_DIR}/Integer.h"
    "${CMAKE_CURRENT_LIST_DIR}/Number.h"
    "${CMAKE_CURRENT_LIST_DIR}/NumberUtils.h"
    "${CMAKE_CURRENT_LIST_DIR}/inttypes.h"
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
        Integer.h Number.h FastRational.h StringMap.h Timer.h inttypes.h
        TreeOps.h Real.h FlaPartitionMap.h PartitionInfo.h ApiException.h TypeUtils.h
        NumberUtils.h NatSet.h ScopedVector.h
DESTINATION ${INSTALL_HEADERS_DIR}/common)
