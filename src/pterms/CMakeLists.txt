add_library(pterms OBJECT "")

target_sources(pterms
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/PtStore.h"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/Pterm.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/PtStore.C"
)

install(FILES Pterm.h PtStore.h DESTINATION ${INSTALL_HEADERS_DIR})

