cmake_minimum_required(VERSION 3.1)
project (opensmt)

set(CMAKE_CXX_STANDARD 11)

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake_modules/")

#message(${CMAKE_C_COMPILER_ID})
#message(${CMAKE_CXX_COMPILER_ID})

set(INSTALL_HEADERS_DIR include/opensmt)

option(PRODUCE_PROOF "Produce proof" OFF)

if(PRODUCE_PROOF)
	add_definitions(-DPRODUCE_PROOF)
	add_subdirectory(proof)
endif()

add_definitions(-DTERMS_HAVE_EXPLANATIONS
 -DUSE_GZ -DFULL_LABELING
)

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
