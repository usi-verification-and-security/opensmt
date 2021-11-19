add_library(sorts OBJECT SStore.cc)

install(FILES SSort.h SStore.h DESTINATION ${INSTALL_HEADERS_DIR})

