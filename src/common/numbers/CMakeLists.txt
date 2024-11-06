target_sources(common
PUBLIC
    "${CMAKE_CURRENT_LIST_DIR}/FastRational.cc"
    "${CMAKE_CURRENT_LIST_DIR}/Integer.h"
    "${CMAKE_CURRENT_LIST_DIR}/Number.h"
    "${CMAKE_CURRENT_LIST_DIR}/Real.h"
PRIVATE
    "${CMAKE_CURRENT_LIST_DIR}/NumberUtils.h"
)

install(FILES
        ${CMAKE_CURRENT_LIST_DIR}/Integer.h
        ${CMAKE_CURRENT_LIST_DIR}/Number.h
        ${CMAKE_CURRENT_LIST_DIR}/NumberCRTP.h
        ${CMAKE_CURRENT_LIST_DIR}/FastRational.h
        ${CMAKE_CURRENT_LIST_DIR}/Real.h
        ${CMAKE_CURRENT_LIST_DIR}/NumberUtils.h
DESTINATION ${INSTALL_HEADERS_DIR}/common/numbers)
