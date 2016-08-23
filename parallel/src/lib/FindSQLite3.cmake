find_path(SQLITE3_INCLUDE_DIR sqlite3.h
        PATHS ${SQLITE3_PATH}/include)

find_library(SQLITE3_LIBRARY NAMES sqlite3
        PATHS ${SQLITE3_PATH}/lib)


if (SQLITE3_INCLUDE_DIR AND SQLITE3_LIBRARY)
    get_filename_component(SQLITE3_LIBRARY_DIR ${SQLITE3_LIBRARY} PATH)
    set(SQLITE3_FOUND TRUE)
endif ()

if (SQLITE3_FOUND)
    message(STATUS "Found SQLITE3: ${SQLITE3_LIBRARY}")
elseif (SQLITE3_FIND_REQUIRED)
    message(FATAL_ERROR "Could not find SQLITE3: use -DSQLITE3_PATH=")
endif ()