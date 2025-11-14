add_library(models OBJECT)

target_sources(models
PUBLIC
    "${CMAKE_CURRENT_SOURCE_DIR}/Model.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/ModelBuilder.h"
PRIVATE
    "${CMAKE_CURRENT_SOURCE_DIR}/Model.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/ModelBuilder.cc"
)

install(FILES Model.h ModelBuilder.h
DESTINATION ${INSTALL_HEADERS_DIR}/models)
