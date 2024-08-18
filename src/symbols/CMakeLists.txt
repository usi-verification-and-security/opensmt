add_library(symbols OBJECT "")

target_sources(symbols
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/Symbol.h"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/SymRef.h"
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/SymStore.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/SymStore.cc"
)

install(FILES Symbol.h SymStore.h SymRef.h DESTINATION ${INSTALL_HEADERS_DIR}/symbols)
