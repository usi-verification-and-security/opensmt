#Fetch and add PTPLib**********************************************************************************************************
set(PTPLib_repository "https://github.com/usi-verification-and-security/partition-channel.git")
set(PTPLib_branch ${branch})
if(NOT PTPLib_branch)
	set(PTPLib_branch master)
endif()

message(STATUS "OpenSMT is fetching PTPLib from " ${PTPLib_repository})
message(STATUS "PTPLib Branch : ${PTPLib_branch}")

include(FetchContent)
Set(FETCHCONTENT_QUIET FALSE)
FetchContent_Declare(
		PTPLib
		GIT_REPOSITORY ${PTPLib_repository}
		GIT_TAG ${PTPLib_branch}
		GIT_SHALLOW true
		GIT_PROGRESS true
)

FetchContent_MakeAvailable(PTPLib)
add_library(PTPLib::PTPLib ALIAS PTPLib)
message(STATUS "PTPLib include: ${PTPLib_SOURCE_DIR}/include")

#add parallel lib and link against PTPLib*******************************************************************************
add_library(parallel OBJECT "")
target_link_libraries(parallel PUBLIC PTPLib::PTPLib)
list(APPEND PRIVATE_SOURCES_TO_ADD
		"${CMAKE_CURRENT_SOURCE_DIR}/ScatterSplitter.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/PreInterpret.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/LookaheadSplitter.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/SplitData.cc"
		"${CMAKE_CURRENT_SOURCE_DIR}/LookaheadSplitter.h"
		"${CMAKE_CURRENT_SOURCE_DIR}/SplitContext.h"
		"${CMAKE_CURRENT_SOURCE_DIR}/SplitData.h"
		"${CMAKE_CURRENT_SOURCE_DIR}/Splitter.h"
)
list(APPEND PUBLIC_SOURCES_TO_ADD
		"${CMAKE_CURRENT_SOURCE_DIR}/MainSplitter.h"
		"${CMAKE_CURRENT_SOURCE_DIR}/ScatterSplitter.h"
		"${CMAKE_CURRENT_SOURCE_DIR}/PreInterpret.h"
)
target_sources(parallel PRIVATE ${PRIVATE_SOURCES_TO_ADD}  PUBLIC ${PUBLIC_SOURCES_TO_ADD} )

if(VERBOSE_SAT)
	target_compile_definitions(parallel PRIVATE -DVERBOSE_SAT)
endif()

if(DEBUG_LOOKAHEAD)
	target_compile_definitions(parallel PRIVATE -DLADEBUG)
endif()

if(PRINT_UNITS)
	target_compile_definitions(parallel PRIVATE -DREPORT_DL1_THLITS)
endif()


#Define OpenSMT-splitter-static library which contains OpenSMT-static, parallel and PTPLib******************************
#Usage: SMTS
if (BUILD_STATIC_LIBS)
	add_library(OpenSMT-splitter-static STATIC "")
	set_target_properties(OpenSMT-splitter-static PROPERTIES
			OUTPUT_NAME opensmt-split
			NO_SYSTEM_FROM_IMPORTED true
			VERSION ${OPENSMT_VERSION}
			ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib"
			)

	target_link_libraries(OpenSMT-splitter-static PUBLIC OpenSMT-static parallel)
	install(TARGETS OpenSMT-splitter-static ARCHIVE DESTINATION lib)
endif()
install(FILES PreInterpret.h DESTINATION ${INSTALL_HEADERS_DIR})



#build splitter executable**********************************************************************************************
if (BUILD_EXECUTABLES)
	add_executable(OpenSMT-bin-splitter opensmtSplitter.cc)
	set_target_properties(OpenSMT-bin-splitter PROPERTIES
			NO_SYSTEM_FROM_IMPORTED true
			OUTPUT_NAME opensmt-splitter
			RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}")
	if (ENABLE_LINE_EDITING)
		if (NOT USE_READLINE)
			find_package(LibEdit REQUIRED)
			target_link_libraries(OpenSMT-bin-splitter PUBLIC LibEdit::LibEdit)
		else()
			find_package(Readline REQUIRED)
			target_link_libraries(OpenSMT-bin-splitter PUBLIC Readline::Readline)
		endif()
	endif()

#link splitter executable against OpenSMT-splitter-static, PTPLib and parallel library**********************************
	target_link_libraries(OpenSMT-bin-splitter PUBLIC OpenSMT-splitter-static parallel)
endif(BUILD_EXECUTABLES)