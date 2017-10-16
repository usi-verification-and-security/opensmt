add_library(cnfizers OBJECT Cnfizer.C TermMapper.C Tseitin.C)
target_include_directories(cnfizers
	PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}" 
	PUBLIC "${CMAKE_SOURCE_DIR}/minisat/mtl" 
	PUBLIC "${CMAKE_SOURCE_DIR}/minisat/core"
	PUBLIC "${CMAKE_SOURCE_DIR}/logics"
	PUBLIC "${CMAKE_SOURCE_DIR}/smtsolvers"
	"${CMAKE_SOURCE_DIR}/pterms"
	)
#target_link_libraries(cnfizers pterms minisat logics smtsolvers)

install(FILES TermMapper.h Tseitin.h Cnfizer.h
DESTINATION ${INSTALL_HEADERS_DIR})

