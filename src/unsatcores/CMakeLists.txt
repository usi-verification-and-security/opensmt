add_library(unsatcores OBJECT)

target_sources(unsatcores
PUBLIC
    "${CMAKE_CURRENT_SOURCE_DIR}/UnsatCore.h"
PRIVATE
    "${CMAKE_CURRENT_SOURCE_DIR}/UnsatCore.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/UnsatCoreBuilder.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/UnsatCoreBuilder.cc"
)

install(FILES UnsatCore.h
DESTINATION ${INSTALL_HEADERS_DIR}/unsatcores)
