add_executable(opensmt opensmt.cc)

if (NOT USE_READLINE)
    find_package(LibEdit REQUIRED)
    target_link_libraries(opensmt PUBLIC ${LibEdit_LIBRARIES})
    target_include_directories(opensmt PUBLIC ${LibEdit_INCLUDE_DIRS})
else()
    find_package(Readline REQUIRED)
    target_link_libraries(opensmt PUBLIC ${Readline_LIBRARY})
    target_include_directories(opensmt PUBLIC ${Readline_INCLUDE_DIRS})
endif()

target_link_libraries(opensmt PUBLIC api_static)

set_target_properties(opensmt PROPERTIES OUTPUT_NAME opensmt)

install(TARGETS opensmt RUNTIME DESTINATION bin)
