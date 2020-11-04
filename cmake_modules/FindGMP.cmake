# Try to find the GMP librairies
# GMP_FOUND - system has GMP lib
# GMP_INCLUDE_DIR - the GMP include directory
# GMP_LIBRARIES - Libraries needed to use GMP

find_path(GMP_INCLUDE_DIR NAMES gmp.h )
find_library(GMP_LIBRARY NAMES gmp libgmp )
find_library(GMPXX_LIBRARY NAMES gmpxx libgmpxx )
mark_as_advanced(GMP_INCLUDE_DIR GMP_LIBRARY GMPXX_LIBRARY)
MESSAGE(STATUS "GMP libs: " ${GMP_LIBRARY} " " ${GMPXX_LIBRARY} )
MESSAGE(STATUS "GMP include: " ${GMP_INCLUDE_DIR})

include(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(GMP DEFAULT_MSG GMP_INCLUDE_DIR GMP_LIBRARY GMPXX_LIBRARY)


if(GMP_FOUND AND NOT TARGET GMP::GMP)
    add_library(GMP::GMP_C UNKNOWN IMPORTED)
    set_target_properties(GMP::GMP_C PROPERTIES
        IMPORTED_LOCATION "${GMP_LIBRARY}"
        INTERFACE_INCLUDE_DIRECTORIES "${GMP_INCLUDE_DIR}"
    )
    
    add_library(GMP::GMP_CXX UNKNOWN IMPORTED)
    set_target_properties(GMP::GMP_CXX PROPERTIES
        IMPORTED_LOCATION "${GMPXX_LIBRARY}"
    )

    add_library(GMP::GMP INTERFACE IMPORTED)
    set_property(TARGET GMP::GMP APPEND PROPERTY
        INTERFACE_LINK_LIBRARIES GMP::GMP_C GMP::GMP_CXX
    )
    set_property(TARGET GMP::GMP APPEND PROPERTY
        INTERFACE_INCLUDE_DIRECTORIES ${GMP_INCLUDE_DIR}
    )
    # the above command is for compatibillity with old versions of CMAKE, the version below is simpler, but works only from CMake 3.11 
    #target_link_libraries(GMP::GMP INTERFACE GMP::GMP_C GMP::GMP_CXX)
endif()
