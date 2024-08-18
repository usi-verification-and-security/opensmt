add_library(cnfizers OBJECT Cnfizer.cc TermMapper.cc Tseitin.cc)

install(FILES TermMapper.h Tseitin.h Cnfizer.h
DESTINATION ${INSTALL_HEADERS_DIR}/cnfizers)
