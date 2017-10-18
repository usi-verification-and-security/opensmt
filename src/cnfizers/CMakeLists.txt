add_library(cnfizers OBJECT Cnfizer.C TermMapper.C Tseitin.C)

install(FILES TermMapper.h Tseitin.h Cnfizer.h
DESTINATION ${INSTALL_HEADERS_DIR})

