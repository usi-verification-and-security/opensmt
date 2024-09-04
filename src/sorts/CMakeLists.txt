add_library(sorts OBJECT)

target_sources(sorts
PUBLIC
    "${CMAKE_CURRENT_SOURCE_DIR}/SSort.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/SStore.h"
PRIVATE
    "${CMAKE_CURRENT_SOURCE_DIR}/SStore.cc"
)

install(FILES SSort.h SStore.h
DESTINATION ${INSTALL_HEADERS_DIR}/sorts)
