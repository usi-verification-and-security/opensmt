# Search for the path containing library's headers
find_path(Readline_ROOT_DIR
    NAMES include/readline/readline.h
)
 
# Search for include directory
find_path(Readline_INCLUDE_DIR
    NAMES readline/readline.h
    HINTS ${Readline_ROOT_DIR}/include
)
 
# Search for library
find_library(Readline_LIBRARY
    NAMES readline
    HINTS ${Readline_ROOT_DIR}/lib
)
 
# Hide these variables in cmake GUIs
mark_as_advanced(
    Readline_ROOT_DIR
    Readline_INCLUDE_DIR
    Readline_LIBRARY
)

MESSAGE(STATUS "Readline library: " ${Readline_LIBRARY} )
include(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(Readline DEFAULT_MSG 
Readline_INCLUDE_DIR Readline_LIBRARY )

if(Readline_FOUND AND NOT TARGET Readline::Readline)
    add_library(Readline::Readline UNKNOWN IMPORTED)
    set_target_properties(Readline::Readline PROPERTIES
        IMPORTED_LOCATION "${Readline_LIBRARY}"
        INTERFACE_INCLUDE_DIRECTORIES "${Readline_INCLUDE_DIR}"
    )
 endif()

