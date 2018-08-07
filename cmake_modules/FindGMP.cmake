# Try to find the GMP librairies
# GMP_FOUND - system has GMP lib
# GMP_INCLUDE_DIR - the GMP include directory
# GMP_LIBRARIES - Libraries needed to use GMP

if (GMP_INCLUDES AND GMP_LIBRARIES)
    set(GMP_FIND_QUIETLY TRUE)
endif (GMP_INCLUDES AND GMP_LIBRARIES)
#
#find_path(GMP_INCLUDES NAMES gmp.h PATHS ENV GMPDIR ${INCLUDE_INSTALL_DIR})

MESSAGE(STATUS "I'm doing GMP stuff now")
#/apps/gmp/6.1.0/gcc-6.1.0/include/gmp.h
find_path(gmp_ROOT_DIR
    NAMES include/gmp.h
    PATHS "/apps/gmp/6.1.0/gcc-6.1.0"
#    NAMES include/readline/readline.h
)

MESSAGE(STATUS "GMP root dir: " ${gmp_ROOT_DIR})

find_path(GMP_INCLUDES
    NAMES gmp.h
    HINTS ${gmp_ROOT_DIR}/include
)

MESSAGE(STATUS "GMP include dir: " ${GMP_INCLUDES})

find_library(GMP_LIBRARY
    NAMES libgmp.so
    HINTS ${gmp_ROOT_DIR}/lib
)
find_library(GMPXX_LIBRARY
    NAMES libgmpxx.so
    HINTS ${gmp_ROOT_DIR}/lib
)

MESSAGE(STATUS "GMP library: " ${GMP_LIBRARY})
MESSAGE(STATUS "GMPXX library: " ${GMPXX_LIBRARY})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(GMP DEFAULT_MSG GMP_INCLUDES GMP_LIBRARY GMPXX_LIBRARY)

mark_as_advanced(GMP_INCLUDES GMP_LIBRARY GMPXX_LIBRARY)
