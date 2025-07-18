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
$<TARGET_OBJECTS:rewriters>
$<TARGET_OBJECTS:unsatcores>
)

add_library(api OBJECT)

set(PRIVATE_SOURCES_TO_ADD
    "${CMAKE_CURRENT_SOURCE_DIR}/GlobalStop.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/MainSolver.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/PartitionManager.cc"
    "${CMAKE_CURRENT_SOURCE_DIR}/Interpret.cc"
)

set(PUBLIC_SOURCES_TO_ADD
    "${CMAKE_CURRENT_SOURCE_DIR}/GlobalStop.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/MainSolver.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/PartitionManager.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/smt2tokens.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/Interpret.h"
    "${CMAKE_CURRENT_SOURCE_DIR}/Opensmt.cc"
)

target_sources(api
PRIVATE ${PRIVATE_SOURCES_TO_ADD}
PUBLIC ${PUBLIC_SOURCES_TO_ADD}
)

set(OBJECTS_TO_ADD $<TARGET_OBJECTS:api> ${OBJECTS_TO_ADD})

if (BUILD_SHARED_LIBS)
    add_library(OpenSMT SHARED ${OBJECTS_TO_ADD})
    set_target_properties(OpenSMT PROPERTIES
        NO_SYSTEM_FROM_IMPORTED true
        VERSION ${OPENSMT_VERSION}
        OUTPUT_NAME opensmt
        LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib"
      )

    target_link_libraries(OpenSMT PUBLIC GMP::GMP Threads::Threads)
    install(TARGETS OpenSMT EXPORT OpenSMTTargets
        LIBRARY DESTINATION lib
        ARCHIVE DESTINATION lib
        RUNTIME DESTINATION bin
        INCLUDES DESTINATION include ${INSTALL_HEADERS_DIR}
    )

    install(EXPORT OpenSMTTargets
        FILE OpenSMTTargets.cmake
        NAMESPACE OpenSMT::
        DESTINATION lib/cmake/opensmt
    )

    include(CMakePackageConfigHelpers)
    write_basic_package_version_file( "${CMAKE_CURRENT_BINARY_DIR}/OpenSMTConfigVersion.cmake"
        VERSION ${OPENSMT_VERSION}
        COMPATIBILITY SameMinorVersion
    )

    configure_package_config_file(OpenSMTConfig.cmake.in
        "${CMAKE_CURRENT_BINARY_DIR}/OpenSMTConfig.cmake"
        INSTALL_DESTINATION lib/cmake/opensmt
    )


    install(FILES
        "${CMAKE_CURRENT_BINARY_DIR}/OpenSMTConfigVersion.cmake"
        "${CMAKE_CURRENT_BINARY_DIR}/OpenSMTConfig.cmake"
        "${PROJECT_SOURCE_DIR}/cmake_modules/FindGMP.cmake"
        DESTINATION lib/cmake/opensmt
    )
endif()

if (BUILD_STATIC_LIBS)
    add_library(OpenSMT-static STATIC ${OBJECTS_TO_ADD})
    set_target_properties(OpenSMT-static PROPERTIES
        OUTPUT_NAME opensmt
        NO_SYSTEM_FROM_IMPORTED true
        VERSION ${OPENSMT_VERSION}
        ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib"
    )

    target_link_libraries(OpenSMT-static PUBLIC GMP::GMP Threads::Threads)
    install(TARGETS OpenSMT-static ARCHIVE DESTINATION lib)
endif()

install(FILES
    Opensmt.h
    smt2tokens.h
    GlobalStop.h
    MainSolver.h
    PartitionManager.h
    Interpret.h
    DESTINATION
    ${INSTALL_HEADERS_DIR}/api
)
