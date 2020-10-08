if(PRINT_DECOMPOSED_STATS)
     target_compile_definitions(tsolvers PRIVATE -DPRINT_DECOMPOSED_STATS)
endif()

target_sources(tsolvers
    PUBLIC "${CMAKE_CURRENT_LIST_DIR}/LRASolver.h"
    #PRIVATE "${CMAKE_CURRENT_LIST_DIR}/LRAModel.h"

    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/LRASolver.cc"
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/LRAModel.cc"

    PUBLIC "${CMAKE_CURRENT_LIST_DIR}/FarkasInterpolator.h"
    PUBLIC "${CMAKE_CURRENT_LIST_DIR}/FarkasInterpolator.cc"
    )

