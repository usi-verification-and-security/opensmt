set(OBJECTS_TO_ADD
$<TARGET_OBJECTS:smtsolvers>
$<TARGET_OBJECTS:parsers>
$<TARGET_OBJECTS:logics>
$<TARGET_OBJECTS:options>
$<TARGET_OBJECTS:symbols>
$<TARGET_OBJECTS:pterms>
$<TARGET_OBJECTS:sorts>
$<TARGET_OBJECTS:tsolvers>
$<TARGET_OBJECTS:cnfizers>
$<TARGET_OBJECTS:common>
$<TARGET_OBJECTS:simplifiers>
$<TARGET_OBJECTS:models>
$<TARGET_OBJECTS:itehandler>
$<TARGET_OBJECTS:proof>
)

add_library(api OBJECT "")

set(PRIVATE_SOURCES_TO_ADD
    "${CMAKE_CURRENT_SOURCE_DIR}/MainSolver.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/PartitionManager.cc"
)

set(PUBLIC_SOURCES_TO_ADD
    "${CMAKE_CURRENT_SOURCE_DIR}/MainSolver.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/PartitionManager.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/smt2tokens.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/Opensmt.cc"
)

target_sources(api
PRIVATE ${PRIVATE_SOURCES_TO_ADD}
PUBLIC ${PUBLIC_SOURCES_TO_ADD}
)

set(OBJECTS_TO_ADD $<TARGET_OBJECTS:api> ${OBJECTS_TO_ADD})

if (BUILD_SHARED_LIBS)
  add_library(opensmt SHARED ${OBJECTS_TO_ADD})
  target_link_libraries(opensmt GMP::GMP Threads::Threads)
  set_target_properties(opensmt PROPERTIES
      VERSION ${OPENSMT_VERSION}
      LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib"
      )
  install(TARGETS opensmt EXPORT opensmtTargets
      LIBRARY DESTINATION lib
      ARCHIVE DESTINATION lib
      RUNTIME DESTINATION bin
      INCLUDES DESTINATION include
      )

  install(EXPORT opensmtTargets
      FILE opensmtTargets.cmake
      NAMESPACE opensmt::
      DESTINATION lib/cmake/opensmt
      )

  include(CMakePackageConfigHelpers)
  write_basic_package_version_file( "${CMAKE_CURRENT_BINARY_DIR}/opensmtConfigVersion.cmake"
    VERSION ${OPENSMT_VERSION}
    COMPATIBILITY SameMinorVersion
    )

  configure_package_config_file(opensmtConfig.cmake.in
    "${CMAKE_CURRENT_BINARY_DIR}/opensmtConfig.cmake"
    INSTALL_DESTINATION lib/cmake/opensmt
    #PATH_VARS INCLUDE_INSTALL_DIR INSTALL_DIR
    )

  install(FILES "${CMAKE_CURRENT_BINARY_DIR}/opensmtConfigVersion.cmake" "${CMAKE_CURRENT_BINARY_DIR}/opensmtConfig.cmake"
    DESTINATION lib/cmake/opensmt
    )
endif()

if (BUILD_STATIC_LIBS)
  add_library(opensmt-static STATIC ${OBJECTS_TO_ADD})
  target_link_libraries(opensmt-static GMP::GMP Threads::Threads)
  set_target_properties(opensmt-static PROPERTIES
      OUTPUT_NAME opensmt
      VERSION ${OPENSMT_VERSION}
      ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib"
      )
  install(TARGETS opensmt-static ARCHIVE DESTINATION lib)
endif()

install(FILES
    Opensmt.h
    smt2tokens.h
    MainSolver.h
    PartitionManager.h
    DESTINATION
    ${INSTALL_HEADERS_DIR}
)
