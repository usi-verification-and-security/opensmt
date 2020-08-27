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
)

set(OBJECTS_TO_ADD $<TARGET_OBJECTS:proof> ${OBJECTS_TO_ADD})

add_library(api OBJECT "")



set(PRIVATE_SOURCES_TO_ADD
	"${CMAKE_CURRENT_SOURCE_DIR}/Interpret.cc"
	"${CMAKE_CURRENT_SOURCE_DIR}/MainSolver.cc"
	"${CMAKE_CURRENT_SOURCE_DIR}/IteManager.cc"
)

set(PUBLIC_SOURCES_TO_ADD
	"${CMAKE_CURRENT_SOURCE_DIR}/Interpret.h"
	"${CMAKE_CURRENT_SOURCE_DIR}/MainSolver.h"
	"${CMAKE_CURRENT_SOURCE_DIR}/DimacsParser.h"
	"${CMAKE_CURRENT_SOURCE_DIR}/IteManager.h"
	"${CMAKE_CURRENT_SOURCE_DIR}/smt2tokens.h"
	"${CMAKE_CURRENT_SOURCE_DIR}/Opensmt.cc"
)

target_sources(api
PRIVATE ${PRIVATE_SOURCES_TO_ADD}
PUBLIC ${PUBLIC_SOURCES_TO_ADD}
)

set(OBJECTS_TO_ADD $<TARGET_OBJECTS:api> ${OBJECTS_TO_ADD})

if (NOT USE_READLINE)
  set(line_library ${LibEdit_LIBRARIES})
else()
  set(line_library ${Readline_LIBRARY})
endif()

if (BUILD_SHARED_LIBS)
  add_library(api_shared SHARED ${OBJECTS_TO_ADD})
  target_link_libraries(api_shared ${line_library} ${GMP_LIBRARIES} ${GMPXX_LIBRARIES} Threads::Threads)
  set_target_properties(api_shared PROPERTIES OUTPUT_NAME opensmt2)
  target_include_directories(api_shared
                             PRIVATE
                             ${LibEdit_INCLUDE_DIRS})
  install(TARGETS api_shared DESTINATION lib)
endif()

if (BUILD_STATIC_LIBS)
  add_library(api_static STATIC ${OBJECTS_TO_ADD})
  target_link_libraries(api_static ${line_library} ${GMP_LIBRARIES} ${GMPXX_LIBRARIES} Threads::Threads)
  target_include_directories(api_static
                             PRIVATE
                             ${LibEdit_INCLUDE_DIRS})
  set_target_properties(api_static PROPERTIES OUTPUT_NAME opensmt2)
endif()

install(FILES Opensmt.h smt2tokens.h MainSolver.h Interpret.h IteManager.h
DESTINATION ${INSTALL_HEADERS_DIR})
