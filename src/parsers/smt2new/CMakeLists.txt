#target_sources(parsers
#PUBLIC "${CMAKE_CURRENT_LIST_DIR}/smt2newcontext.h"
#PUBLIC "${CMAKE_CURRENT_LIST_DIR}/smt2newparser.hh"
#PRIVATE "${CMAKE_CURRENT_LIST_DIR}/smt2newcontext.cc"
#PRIVATE "${CMAKE_CURRENT_LIST_DIR}/smt2newlexer.cc"
#PRIVATE "${CMAKE_CURRENT_LIST_DIR}/smt2newparser.cc"
#)

add_library(parsers OBJECT "")

find_package(BISON 3.0 REQUIRED)
find_package(FLEX 2.6 REQUIRED)

BISON_TARGET(smt2newParser smt2newparser.yy ${CMAKE_CURRENT_BINARY_DIR}/smt2newparser.cc)
FLEX_TARGET(smt2newScanner smt2newlexer.ll ${CMAKE_CURRENT_BINARY_DIR}/smt2newlexer.cc)
ADD_FLEX_BISON_DEPENDENCY(smt2newScanner smt2newParser)

target_sources(parsers
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/smt2newcontext.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/smt2newcontext.h"
    PRIVATE ${BISON_smt2newParser_OUTPUTS}
    PRIVATE ${FLEX_smt2newScanner_OUTPUTS}
)

target_compile_options(parsers PRIVATE -Wno-error)

install(FILES smt2newcontext.h
DESTINATION ${INSTALL_HEADERS_DIR}/parsers/smt2new)
