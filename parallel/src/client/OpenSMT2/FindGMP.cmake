find_path(GMP_INCLUDE_DIR gmp.h gmpxx.h
        PATHS ${GMP_PATH}/include)

find_library(GMP_LIBRARY NAMES gmp
        PATHS ${GMP_PATH}/lib)


if (GMP_INCLUDE_DIR AND GMP_LIBRARY)
    get_filename_component(GMP_LIBRARY_DIR ${GMP_LIBRARY} PATH)
    set(GMP_FOUND TRUE)
endif ()

if (GMP_FOUND)
    message(STATUS "Found GMP: ${GMP_LIBRARY}")
elseif (GMP_FIND_REQUIRED)
    message(FATAL_ERROR "Could not find GMP: use -DGMP_PATH=")
endif ()
