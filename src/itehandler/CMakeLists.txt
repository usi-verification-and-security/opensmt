add_library(itehandler OBJECT IteToSwitch.cc IteToSwitchMisc.cc IteHandler.cc)
install(FILES IteToSwitch.h IteHandler.h DESTINATION ${INSTALL_HEADERS_DIR})

