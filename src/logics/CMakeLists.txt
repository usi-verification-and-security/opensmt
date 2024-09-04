add_library(logics OBJECT)

target_sources(logics
PUBLIC
    "${CMAKE_CURRENT_SOURCE_DIR}/Logic.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/ArithLogic.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/BVLogic.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/LogicFactory.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/Theory.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/FunctionTools.h"
PRIVATE
    "${CMAKE_CURRENT_SOURCE_DIR}/LogicFactory.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/BVLogic.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/Logic.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/ArrayTheory.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/ArrayHelpers.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/ArithLogic.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/LATheory.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/UFLATheory.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/UFLATheory.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/UFTheory.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/SubstLoopBreaker.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/SubstLoopBreaker.cc"
)

install(FILES LogicFactory.h Theory.h Logic.h ArithLogic.h BVLogic.h FunctionTools.h
DESTINATION ${INSTALL_HEADERS_DIR}/logics)
