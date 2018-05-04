include(GoogleTest)
add_executable(LRATest)
target_sources(LRATest 
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Rationals.cpp"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Delta.cpp"
    )

target_link_libraries(LRATest api_static gtest gtest_main)

gtest_add_tests(TARGET LRATest)
