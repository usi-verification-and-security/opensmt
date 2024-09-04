add_library(options OBJECT)

target_sources(options
PUBLIC
    "${CMAKE_CURRENT_SOURCE_DIR}/SMTConfig.h"
PRIVATE
    "${CMAKE_CURRENT_SOURCE_DIR}/SMTConfig.cc"
)

install(FILES SMTConfig.h
DESTINATION ${INSTALL_HEADERS_DIR}/options)
