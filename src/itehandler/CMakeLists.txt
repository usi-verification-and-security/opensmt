add_library(itehandler OBJECT)

target_sources(itehandler
PRIVATE
    "${CMAKE_CURRENT_SOURCE_DIR}/IteToSwitch.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/IteToSwitch.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/IteToSwitchMisc.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/IteHandler.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/IteHandler.cc"
)
