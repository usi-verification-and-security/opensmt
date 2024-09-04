add_library(cnfizers OBJECT)

target_sources(cnfizers
PUBLIC
    "${CMAKE_CURRENT_SOURCE_DIR}/Cnfizer.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/TermMapper.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/Tseitin.h"
PRIVATE
    "${CMAKE_CURRENT_SOURCE_DIR}/Cnfizer.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/TermMapper.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/Tseitin.cc"
)

install(FILES TermMapper.h Tseitin.h Cnfizer.h
DESTINATION ${INSTALL_HEADERS_DIR}/cnfizers)
