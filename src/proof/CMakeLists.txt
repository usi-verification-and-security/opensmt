add_library(proof OBJECT)

target_sources(proof
PUBLIC
    "${CMAKE_CURRENT_SOURCE_DIR}/InterpolationContext.h"
PRIVATE
    "${CMAKE_CURRENT_SOURCE_DIR}/PG.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/PGBuild.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/PGCheck.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/PGHelp.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/PGHeuristics.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/PGMain.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/PGPrint.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/PGRules.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/PGTransformationAlgorithms.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/InterpolationContext.cc"
)

install(FILES InterpolationContext.h
DESTINATION ${INSTALL_HEADERS_DIR}/proof)
