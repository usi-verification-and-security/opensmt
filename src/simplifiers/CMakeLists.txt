add_library(simplifiers STATIC "")

target_sources(simplifiers
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/LA.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/LA.C"
)

target_include_directories(simplifiers
PRIVATE "${CMAKE_SOURCE_DIR}/logics"
PRIVATE "${CMAKE_SOURCE_DIR}/tsolvers"
PRIVATE "${CMAKE_SOURCE_DIR}/pterms"
)

target_link_libraries(simplifiers pterms)
