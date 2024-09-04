add_library(rewriters OBJECT)

target_sources(rewriters
PUBLIC
    "${CMAKE_CURRENT_SOURCE_DIR}/Substitutor.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/Rewriter.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/Rewritings.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/Rewritings.cc"
)

install(FILES
    Substitutor.h
    Rewriter.h
    Rewritings.h
DESTINATION ${INSTALL_HEADERS_DIR}/rewriters)
