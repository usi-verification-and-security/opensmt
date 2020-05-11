add_executable(exec opensmt.cc)

target_link_libraries(exec api_static)

set_target_properties(exec PROPERTIES OUTPUT_NAME opensmt)

install(TARGETS exec RUNTIME DESTINATION bin)
