target_sources(tsolvers
    PUBLIC "${CMAKE_CURRENT_LIST_DIR}/LRASolver.h"
    #PRIVATE "${CMAKE_CURRENT_LIST_DIR}/LRAModel.h"

    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/LRASolver.cc"
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/LRAModel.cc"
    )

target_sources(tsolvers
    PUBLIC "${CMAKE_CURRENT_LIST_DIR}/LRA_Interpolator.h"
    PUBLIC "${CMAKE_CURRENT_LIST_DIR}/LRA_Interpolator.cc"
    )

