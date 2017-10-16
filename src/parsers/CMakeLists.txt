add_library(parsers OBJECT "")

target_include_directories(parsers
INTERFACE "${CMAKE_CURRENT_SOURCE_DIR}/smt2new"
)

include(smt2new/CMakeLists.txt)

