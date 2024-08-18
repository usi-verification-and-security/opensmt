add_library(options OBJECT SMTConfig.cc)

install(FILES SMTConfig.h DESTINATION ${INSTALL_HEADERS_DIR}/options)
