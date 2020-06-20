# Find LibEdit
# LibEdit_FOUND - found LibEdit lib
# LibEdit_INCLUDE_DIR - the LibEdit include directory
# LibEdit_LIBRARIES - Libraries needed to use LibEdit

find_path(LibEdit_INCLUDE_DIR NAMES histedit.h)
find_library(LibEdit_LIBRARIES NAMES edit libedit)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(LibEdit
  DEFAULT_MSG LibEdit_INCLUDE_DIR LibEdit_LIBRARIES)

mark_as_advanced(LibEdit_INCLUDE_DIR LibEdit_LIBRARIES)
if(LibEdit_LIBRARIES)
  message(STATUS "LibEdit library: ${LibEdit_LIBRARIES}")
endif()

