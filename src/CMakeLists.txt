set(PTPLib_repository "https://github.com/usi-verification-and-security/partition-channel.git")
set(PTPLib_branch ${branch})
if(NOT PTPLib_branch )
  set(PTPLib_branch protocol_example)
endif()
message("-- OpenSMT is fetching PTPLib from " ${PTPLib_repository})
message("-- PTPLib Branch : ${PTPLib_branch}")

include(FetchContent)
FetchContent_Declare(
        PTPLib
        GIT_REPOSITORY ${PTPLib_repository}
        GIT_TAG ${PTPLib_branch}
)

FetchContent_MakeAvailable(PTPLib)

add_library(PTPLib::PTPLib ALIAS PTPLib)

message("-- PTPLib files have been written to: ${PTPLib_SOURCE_DIR}")
execute_process(COMMAND ${CMAKE_CURRENT_LIST_DIR}/remove_PTPLib_tests.sh ${PTPLib_SOURCE_DIR} RESULT_VARIABLE res)

add_subdirectory(proof)
add_subdirectory(common)
add_subdirectory(cnfizers)
add_subdirectory(pterms)
add_subdirectory(symbols)
add_subdirectory(sorts)
add_subdirectory(options)
add_subdirectory(api)
add_subdirectory(minisat)
add_subdirectory(models)
add_subdirectory(logics)
add_subdirectory(tsolvers)
add_subdirectory(simplifiers)
add_subdirectory(smtsolvers)
add_subdirectory(parsers)
add_subdirectory(itehandler)
add_subdirectory(rewriters)
add_subdirectory(interpolation)
if (BUILD_EXECUTABLES)
  add_subdirectory(bin)
endif()
