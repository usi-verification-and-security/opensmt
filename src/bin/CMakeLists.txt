add_executable(opensmt-bin opensmt.cc Interpret.cc)

set_target_properties(opensmt-bin PROPERTIES
    NO_SYSTEM_FROM_IMPORTED true # For some reason on MAC OS build in travis, the .cc files from this target were compiled with -isystem /usr/include and that was messing up the search order of include paths; This seems to fix it
    OUTPUT_NAME opensmt
    RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}")

if (NOT USE_READLINE)
    find_package(LibEdit REQUIRED)
    target_link_libraries(opensmt-bin PUBLIC LibEdit::LibEdit)
else()
    find_package(Readline REQUIRED)
    target_link_libraries(opensmt-bin PUBLIC Readline::Readline)
endif()

target_link_libraries(opensmt-bin PUBLIC opensmt-static)


install(TARGETS opensmt-bin RUNTIME DESTINATION bin)
