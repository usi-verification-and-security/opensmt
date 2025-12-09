add_library(common OBJECT)

target_sources(common
PUBLIC
    "${CMAKE_CURRENT_LIST_DIR}/FlaPartitionMap.cc"
    "${CMAKE_CURRENT_LIST_DIR}/IColor.h"
    "${CMAKE_CURRENT_LIST_DIR}/Partitions.h"
    "${CMAKE_CURRENT_LIST_DIR}/TermNames.h"
PRIVATE
    "${CMAKE_CURRENT_LIST_DIR}/SystemQueries.h"
    "${CMAKE_CURRENT_LIST_DIR}/inttypes.h"
    "${CMAKE_CURRENT_LIST_DIR}/StringMap.h"
    "${CMAKE_CURRENT_LIST_DIR}/StringConv.h"
    "${CMAKE_CURRENT_LIST_DIR}/Timer.h"
    "${CMAKE_CURRENT_LIST_DIR}/TreeOps.h"
    "${CMAKE_CURRENT_LIST_DIR}/NatSet.h"
    "${CMAKE_CURRENT_LIST_DIR}/PartitionInfo.cc"
    "${CMAKE_CURRENT_LIST_DIR}/VerificationUtils.cc"
    "${CMAKE_CURRENT_LIST_DIR}/ReportUtils.h"
    "${CMAKE_CURRENT_LIST_DIR}/polynomials/Translations.cc"
)

include(numbers/CMakeLists.txt)

install(FILES
        StringMap.h Timer.h inttypes.h IColor.h
        TreeOps.h FlaPartitionMap.h PartitionInfo.h Partitions.h ApiException.h TypeUtils.h
        NatSet.h ScopedVector.h TermNames.h NonLinException.h
DESTINATION ${INSTALL_HEADERS_DIR}/common)
