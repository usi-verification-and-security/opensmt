cmake_minimum_required(VERSION 3.1)
project (opensmt)

set(CMAKE_CXX_STANDARD 11)

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake_modules/")

set(CMAKE_POSITION_INDEPENDENT_CODE ON)

message(${CMAKE_C_COMPILER_ID})
message(${CMAKE_CXX_COMPILER_ID})

set(INSTALL_HEADERS_DIR include/opensmt)

option(PRODUCE_PROOF "Produce proof" OFF)

add_definitions(-DTERMS_HAVE_EXPLANATIONS
 -DUSE_GZ -DOPTIMIZE
)

include_directories(
${CMAKE_SOURCE_DIR}/minisat/mtl
${CMAKE_SOURCE_DIR}/minisat/core
${CMAKE_SOURCE_DIR}/common
${CMAKE_SOURCE_DIR}/sorts
${CMAKE_SOURCE_DIR}/symbols
${CMAKE_SOURCE_DIR}/options
${CMAKE_SOURCE_DIR}/api
${CMAKE_SOURCE_DIR}/tsolvers
${CMAKE_SOURCE_DIR}/tsolvers/egraph
${CMAKE_SOURCE_DIR}/tsolvers/lrasolver
${CMAKE_SOURCE_DIR}/cnfizers
${CMAKE_SOURCE_DIR}/pterms
${CMAKE_SOURCE_DIR}/logics
${CMAKE_SOURCE_DIR}/smtsolvers
${CMAKE_SOURCE_DIR}/parsers/smt2new
${CMAKE_SOURCE_DIR}/simplifiers
)

if(PRODUCE_PROOF)
	add_definitions(-DPRODUCE_PROOF -DFULL_LABELING)
	include_directories(${CMAKE_SOURCE_DIR}/proof)
	add_subdirectory(proof)
endif()


add_subdirectory(common)
add_subdirectory(cnfizers)
add_subdirectory(pterms)
add_subdirectory(symbols)
add_subdirectory(sorts)
add_subdirectory(options)
add_subdirectory(api)
add_subdirectory(minisat)
add_subdirectory(logics)
add_subdirectory(tsolvers)
add_subdirectory(simplifiers)
add_subdirectory(smtsolvers)
add_subdirectory(parsers) 
add_subdirectory(bin)

install(FILES opensmt2.h DESTINATION ${INSTALL_HEADERS_DIR})
