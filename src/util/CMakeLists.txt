add_library(util OBJECT)

set(OPENSMT_GIT_DESCRIPTION "\"${OPENSMT_GIT_DESCRIPTION}\"")
configure_file(opensmt_version.h.cmake.in ${CMAKE_CURRENT_SOURCE_DIR}/opensmt_version.h)

target_sources(util
        PUBLIC
        "${CMAKE_CURRENT_SOURCE_DIR}/opensmt_version.h"
)

install(FILES opensmt_version.h
        DESTINATION ${INSTALL_HEADERS_DIR}/util)
