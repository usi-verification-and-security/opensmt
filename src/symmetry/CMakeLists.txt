add_library(symmetry STATIC Symmetry.h Symmetry.cpp)

target_include_directories(symmetry
PRIVATE "${CMAKE_SOURCE_DIR}"
)

target_link_libraries(symmetry logics)
