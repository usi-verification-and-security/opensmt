add_library(sorts OBJECT SSort.cc SStore.cc)

install(FILES SSort.h SStore.h DESTINATION ${INSTALL_HEADERS_DIR})

