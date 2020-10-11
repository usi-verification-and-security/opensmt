add_executable(opensmt-bin opensmt.cc Interpret.cc)

if (NOT USE_READLINE)
    find_package(LibEdit REQUIRED)
    target_link_libraries(opensmt-bin PUBLIC LibEdit::LibEdit)
else()
    find_package(Readline REQUIRED)
    target_link_libraries(opensmt-bin PUBLIC Readline::Readline)
endif()

target_link_libraries(opensmt-bin PUBLIC opensmt-static)

set_target_properties(opensmt-bin PROPERTIES OUTPUT_NAME opensmt RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}")

install(TARGETS opensmt-bin RUNTIME DESTINATION bin)
