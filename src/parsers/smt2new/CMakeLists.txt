target_sources(parsers
PUBLIC "${CMAKE_CURRENT_LIST_DIR}/smt2newcontext.h"
PUBLIC "${CMAKE_CURRENT_LIST_DIR}/smt2newparser.hh"
PRIVATE "${CMAKE_CURRENT_LIST_DIR}/smt2newcontext.cc"
PRIVATE "${CMAKE_CURRENT_LIST_DIR}/smt2newlexer.cc"
PRIVATE "${CMAKE_CURRENT_LIST_DIR}/smt2newparser.cc"
)

target_link_libraries(parsers options)

target_include_directories(parsers
PRIVATE "${CMAKE_SOURCE_DIR}/options"
)
