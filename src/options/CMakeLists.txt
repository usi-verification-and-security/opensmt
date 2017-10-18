add_library(options OBJECT SMTConfig.C)

install(FILES SMTConfig.h DESTINATION ${INSTALL_HEADERS_DIR})
