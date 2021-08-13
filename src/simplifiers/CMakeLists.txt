add_library(simplifiers OBJECT "")

target_sources(simplifiers
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/LA.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/LA.cc"
        "${CMAKE_CURRENT_SOURCE_DIR}/BoolRewriting.cc"
)

install(FILES BoolRewriting.h
    DESTINATION ${INSTALL_HEADERS_DIR}
    )
