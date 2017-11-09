#add_library(parsers OBJECT "")
#
#find_package(BISON)
#find_package(FLEX)
#
#BISON_TARGET(smt2newParser smt2new/smt2newparser.yy ${CMAKE_CURRENT_BINARY_DIR}/smt2new/smt2newparser.cc)
#FLEX_TARGET(smt2newScanner smt2new/smt2newlexer.ll ${CMAKE_CURRENT_BINARY_DIR}/smt2new/smt2newlexer.cc)
#ADD_FLEX_BISON_DEPENDENCY(smt2newScanner smt2newParser)
#
#target_sources(parsers
#    PUBLIC "smt2new/smt2newcontext.cc"
#    PUBLIC "smt2new/smt2newcontext.h"
#    PRIVATE ${BISON_smt2newParser_OUTPUTS}
#    PRIVATE ${FLEX_smt2newScanner_OUTPUTS}
#)
add_subdirectory(smt2new)
