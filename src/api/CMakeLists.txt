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
)

set(OBJECTS_TO_ADD $<TARGET_OBJECTS:proof> ${OBJECTS_TO_ADD})

add_library(api OBJECT "")



set(PRIVATE_SOURCES_TO_ADD
	"${CMAKE_CURRENT_SOURCE_DIR}/Interpret.cc"
	"${CMAKE_CURRENT_SOURCE_DIR}/MainSolver.cc"
)

set(PUBLIC_SOURCES_TO_ADD
	"${CMAKE_CURRENT_SOURCE_DIR}/Interpret.h"
	"${CMAKE_CURRENT_SOURCE_DIR}/MainSolver.h"
	"${CMAKE_CURRENT_SOURCE_DIR}/DimacsParser.h"
	"${CMAKE_CURRENT_SOURCE_DIR}/smt2tokens.h"
	"${CMAKE_CURRENT_SOURCE_DIR}/Opensmt.cc"
)

target_sources(api
PRIVATE ${PRIVATE_SOURCES_TO_ADD}
PUBLIC ${PUBLIC_SOURCES_TO_ADD}
)

set(OBJECTS_TO_ADD $<TARGET_OBJECTS:api> ${OBJECTS_TO_ADD})

if (BUILD_SHARED_LIBS)
  add_library(api_shared SHARED ${OBJECTS_TO_ADD})
  target_link_libraries(api_shared ${GMP_LIBRARIES} ${GMPXX_LIBRARIES} Threads::Threads)
  set_target_properties(api_shared PROPERTIES 
      OUTPUT_NAME opensmt
      VERSION ${OPENSMT_VERSION}
      LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib"
      )
  install(TARGETS api_shared LIBRARY DESTINATION lib)
endif()

if (BUILD_STATIC_LIBS)
  add_library(api_static STATIC ${OBJECTS_TO_ADD})
  target_link_libraries(api_static ${GMP_LIBRARIES} ${GMPXX_LIBRARIES} Threads::Threads)
  set_target_properties(api_static PROPERTIES 
      OUTPUT_NAME opensmt
      VERSION ${OPENSMT_VERSION}
      ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib"
      )
  install(TARGETS api_static LIBRARY DESTINATION lib)
endif()

install(FILES Opensmt.h smt2tokens.h MainSolver.h Interpret.h DESTINATION ${INSTALL_HEADERS_DIR})
