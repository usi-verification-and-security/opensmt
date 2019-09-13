target_sources(tsolvers
    PUBLIC "${CMAKE_CURRENT_LIST_DIR}/LASolver.h"
    PUBLIC "${CMAKE_CURRENT_LIST_DIR}/Simplex.h"
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/LASolver.C"
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/Simplex.cpp"
    )



