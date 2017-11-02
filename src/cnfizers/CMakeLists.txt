add_library(cnfizers OBJECT Cnfizer.C TermMapper.C Tseitin.C CnfState.h)

install(FILES TermMapper.h Tseitin.h Cnfizer.h CnfState.h
DESTINATION ${INSTALL_HEADERS_DIR})

