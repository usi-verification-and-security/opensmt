# Find LibEdit
# LibEdit_FOUND - found LibEdit lib
# LibEdit_INCLUDE_DIR - the LibEdit include directory
# LibEdit_LIBRARIES - Libraries needed to use LibEdit

find_path(LibEdit_INCLUDE_DIR NAMES histedit.h)
find_library(LibEdit_LIBRARY NAMES edit libedit)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(LibEdit
  DEFAULT_MSG LibEdit_INCLUDE_DIR LibEdit_LIBRARY)

message(STATUS "LibEdit library: ${LibEdit_LIBRARY}")
mark_as_advanced(LibEdit_INCLUDE_DIR LibEdit_LIBRARY)

if(LibEdit_FOUND AND NOT TARGET LibEdit::LibEdit)
    add_library(LibEdit::LibEdit UNKNOWN IMPORTED)
    set_target_properties(LibEdit::LibEdit PROPERTIES
        IMPORTED_LOCATION "${LibEdit_LIBRARY}"
        INTERFACE_INCLUDE_DIRECTORIES "${LibEdit_INCLUDE_DIR}"
    )
 endif()

