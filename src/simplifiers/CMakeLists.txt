add_library(simplifiers OBJECT "")

target_sources(simplifiers
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/LA.h"
PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/LA.C"
    "${CMAKE_CURRENT_SOURCE_DIR}/BoolRewriting.cpp"
)
