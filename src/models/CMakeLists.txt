add_library(models OBJECT)

target_sources(models
PUBLIC
    "${CMAKE_CURRENT_SOURCE_DIR}/Model.h"
PRIVATE
    "${CMAKE_CURRENT_SOURCE_DIR}/Model.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/ModelBuilder.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/ModelBuilder.cc"
)

install(FILES Model.h
DESTINATION ${INSTALL_HEADERS_DIR}/models)
