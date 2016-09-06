function(contrib PACKAGE DEPENDENCY)
    include(${CMAKE_SOURCE_DIR}/src/contrib/${PACKAGE}_PACKAGE.cmake)
    PACKAGE()
    if (NOT ${PACKAGE}_PACKAGE)
        return()
    endif ()
    message(STATUS "Using ${PACKAGE}_PACKAGE: ${${PACKAGE}_PACKAGE}")
    include(ExternalProject)
    ExternalProject_Add(${PACKAGE}
            URL ${${PACKAGE}_PACKAGE}
            UPDATE_COMMAND ""
            PATCH_COMMAND ""
            CONFIGURE_COMMAND ""
            BUILD_COMMAND ""
            INSTALL_COMMAND ""
            )
    ExternalProject_Get_Property(${PACKAGE} SOURCE_DIR)
    set(${PACKAGE}_INCLUDE_DIR ${SOURCE_DIR}${${PACKAGE}_INCLUDE_DIR_SUFFIX} PARENT_SCOPE)
    set(${PACKAGE}_LIBRARY ${SOURCE_DIR}${${PACKAGE}_LIBRARY_SUFFIX} PARENT_SCOPE)
    add_dependencies(${DEPENDENCY} ${PACKAGE})
endfunction()