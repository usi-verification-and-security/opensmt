# Try to find the GMP librairies
# GMP_FOUND - system has GMP lib
# GMP_INCLUDE_DIR - the GMP include directory
# GMP_LIBRARIES - Libraries needed to use GMP

if(FORCE_STATIC_GMP)
    #message("Trying to find static version of GMP")
    find_library(GMP_LIBRARY NAMES libgmp.a REQUIRED)
    find_library(GMPXX_LIBRARY NAMES libgmpxx.a REQUIRED)
    if(NOT ${GMP_LIBRARY} MATCHES ".*\.a$" OR NOT ${GMPXX_LIBRARY} MATCHES ".*\.a$")
        MESSAGE(WARNING
                "Failed to find static libraries for GMP or GMPXX.\n"
                "Hint: Try clearing CMakeCache.txt and request static libs on command line.  "
                "cmake will not switch to static libraries if it was previously configured "
                "with shared libraries. ")
        MESSAGE(SEND_ERROR "Static GMP libs were not found")
    endif()
endif(FORCE_STATIC_GMP)

find_library(GMP_LIBRARY NAMES gmp)
find_library(GMPXX_LIBRARY NAMES gmpxx)
find_path(GMP_INCLUDE_DIR NAMES gmp.h)
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
    target_link_libraries(GMP::GMP INTERFACE GMP::GMP_CXX GMP::GMP_C)
endif()
