target_sources(tsolvers
    PUBLIC "${CMAKE_CURRENT_LIST_DIR}/LRASolver.h"
    #PRIVATE "${CMAKE_CURRENT_LIST_DIR}/LRAModel.h"

    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/LRASolver.cpp"
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/LRAModel.cpp"
    )

if(PRODUCE_PROOF)
    target_sources(tsolvers
        PUBLIC "${CMAKE_CURRENT_LIST_DIR}/LRA_Interpolator.h"
        PUBLIC "${CMAKE_CURRENT_LIST_DIR}/LRA_Interpolator.cpp"
        )
endif()

