add_library(rewriters OBJECT "")

target_sources(rewriters
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/DistinctRewriter.cc"
)

install(FILES Rewriter.h Substitutor.h ArithmeticEqualityRewriter.h
    DESTINATION ${INSTALL_HEADERS_DIR})