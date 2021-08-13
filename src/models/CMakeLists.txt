add_library(models OBJECT Model.cc ModelBuilder.cc)

install(FILES Model.h FunctionTools.h ModelBuilder.h
    DESTINATION ${INSTALL_HEADERS_DIR})
