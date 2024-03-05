add_executable(OpenSMT-bin opensmt.cc)

set_target_properties(OpenSMT-bin PROPERTIES
    NO_SYSTEM_FROM_IMPORTED true # For some reason on MAC OS build in travis, the .cc files from this target were compiled with -isystem /usr/include and that was messing up the search order of include paths; This seems to fix it
    OUTPUT_NAME opensmt
    RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}")

if (ENABLE_LINE_EDITING)
    find_package(LibEdit REQUIRED)
    target_link_libraries(OpenSMT-bin PUBLIC LibEdit::LibEdit)
endif()

target_link_libraries(OpenSMT-bin PUBLIC OpenSMT-static)


install(TARGETS OpenSMT-bin RUNTIME DESTINATION bin)
