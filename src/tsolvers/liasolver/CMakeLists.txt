target_sources(tsolvers
    PUBLIC "${CMAKE_CURRENT_LIST_DIR}/Matrix.h"
    PUBLIC "${CMAKE_CURRENT_LIST_DIR}/LIAInterpolator.h"

    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/Matrix.cc"
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/LIAInterpolator.cc"

)

