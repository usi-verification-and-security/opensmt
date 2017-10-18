add_library(sorts OBJECT SSort.C SStore.C)

install(FILES SSort.h SStore.h DESTINATION ${INSTALL_HEADERS_DIR})

