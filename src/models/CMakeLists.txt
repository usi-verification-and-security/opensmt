add_library(models OBJECT Model.cc ModelBuilder.cc)

install(FILES Model.h 
    DESTINATION ${INSTALL_HEADERS_DIR}/models)
